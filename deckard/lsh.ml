module C = Context
module D = Deckard_types
module Cv = Charv

(* number of characteristic vectors in our dataset *)
let n = ref 0

(* number of hashing functions *)
let k = ref 0
let l = ref 0

(* probabilities are calculated further down *)
let p1 = ref 0.
let p2 = ref 0.

(* helpers *)
(* make int list of size n *)
let rec create_list n =
    if n>0 then 0::(create_list (n-1)) else []

let rec create_hash_from_list ints =
    match ints with
    | x::xs -> (string_of_int x) ^ (create_hash_from_list xs)
    | [] -> ""

(* math *)
module M = (
    struct
        (* why isn't round and pi in pervasives? *)
        let round x = int_of_float (if x >= (floor x +. 0.5) then ceil x else floor x)
        let pi = acos (-1.)

        (* logarithmic identities at work *)
        let log_y base x = (log x) /. (log base)

        (* reciprocal value *)
        let recip x = 1. /. x

        (* probability calculation - watch out for sigmas *)
        let f2 x =
            Gc.major ();
            ((sqrt 2.) /. ( sqrt pi )) *. exp ( -. ((x ** 2.) /. 2. ))

        let pdf_content c t =
            Gc.major ();
            (1. /. c) *. f2 (t /. c) *. (1. -. (t /. !C.r))

        let compute_prob x =
            let gslfun = pdf_content x in
            let ws = Gsl_integration.make_ws 1000 in
            let {Gsl_fun.res = res; Gsl_fun.err=err} = Gsl_integration.qags gslfun
            ~a:0. ~b:!C.r ~epsabs:0. ~epsrel:1e-7 ws in
            (res, ( err, Gsl_integration.size ws))
    end
    :
    sig
        val round : float -> int
        val log_y : float -> float -> float
        val recip : float -> float
        val compute_prob : float -> float * ( float * int )
    end
)


module type SAMPLER = (
    sig
        type t
        val create : unit -> t
        val get_a : t -> float list
        val get_b : t -> float
    end )

module Sampler : SAMPLER = (
    struct
        type t = { a : float list; b : float }
        let _ = Gsl_error.init (); Gsl_rng.env_setup()
        let rng_a = Gsl_rng.make (Gsl_rng.default ())
        let rng_b = Gsl_rng.make (Gsl_rng.default ())
        let gaussian s = Gsl_randist.gaussian rng_a ~sigma:s
        let uniform r = Gsl_randist.flat rng_b ~a:0. ~b:r
        (* generate vectors with values from gaussian distribution *)
        let create_a () =
            (* we use sigma = 1 everywhere anyway? *)
            (* let sigma = C.sigma in *)
            let sigma = 1. in
            let dim = D.dimensions in
            let rec g d =
                if d<>0 then
                (gaussian sigma)::(g (d-1))
                else []
            in
            g dim
        (* generate a random value for the window size *)
        let create_b () =
            uniform !C.r
        (* return a sample *)
        let create () = { a = create_a (); b = create_b () }
        let get_a s = s.a
        let get_b s = s.b
    end
)

(* functor returning a hash function sampled from parameter *)
(*module type HASH =
    sig
        type t
        val create : unit -> t
        val hash : t -> Cv.charv -> int
    end
*)

(* G instances *)
module G = functor (S : SAMPLER) ->
    (
    struct
        module H = functor ( Q : SAMPLER ) ->
        (
            struct
                type t = { c : Q.t }
                let create () = { c = Q.create () }
                let hash h v =
                    let s = h.c in
                    let innerproduct s v = Charv.innerproduct s v in
                    let a = Q.get_a s in
                    let b = Q.get_b s in
                    int_of_float (floor(((innerproduct a v) +. b) /. !C.r))
            end
        )

        module Hash = H(S)

        type t = { c : Hash.t list }
        let create n =
            (* generate list of hashes *)
            let t_list = List.map (fun _ -> Hash.create ()) (create_list n) in
            (* return list of hashes *)
            { c = t_list }
        let hash t v = create_hash_from_list (List.map (fun x -> Hash.hash x v)
                                              t.c )
    end
    :
    sig
        type t
        val create : int -> t
        val hash : t -> Cv.charv -> string
    end
)

module type GHASH =
    sig
        type t
        val create : int -> t
        val hash : t -> Cv.charv -> string
    end


(* the LSH hash db *)

module LshDb = (
    struct
        module Gs = G (Sampler)
        (* hashers are probably redundant *)
        type t = { hashers : Gs.t list ;
                   table : (Gs.t, (string, C.vstore_t list) Hashtbl.t)
                           Hashtbl.t ;
                   map : (C.vstore_t, (Gs.t * string) list) Hashtbl.t
                 }

        let setup size =
            (*let size = List.length vectors in *)
            let nf = float_of_int size in
            let p p1 p2= ((log (M.recip p1)) /. (log (M.recip p2))) in

            n := size;

            (* calculate the probabilities for our hash function given parameters *)
            Gsl_error.init ();
            p1 := fst (M.compute_prob 1.);
            p2 := fst (M.compute_prob !C.c);

            (* calculate parameters guarding number of different hashes etc *)
            k := M.round (M.log_y (M.recip !p2) nf);
            l := M.round (nf ** (p !p1 !p2))

        (* outer table - keys are hash functions, values are hash tables *)

        let create_gs k l =
            List.map (fun _ -> Gs.create k) (create_list l)

        let create_tables gs n =
            let outertbl = Hashtbl.create !l in
            List.iter (fun x ->
                           let inner = Hashtbl.create n in
                           Hashtbl.add outertbl x inner
                      ) gs;
            outertbl

        let add t v =
            let find table key = (
                try
                    Hashtbl.find table key
                with Not_found ->
                    [] ) in
            let gs = t.hashers in
            let outer = t.table in
            let map = t.map in
            let mapping = List.map (fun x -> (x, Gs.hash x (fst v))) gs in
            List.iter (fun x -> let hashfunc = fst x in
                                let hash = snd x in
                                let inner = Hashtbl.find outer hashfunc in
                                let cur = find inner hash in
                                if cur <> [] then
                                    Hashtbl.replace inner hash (v::cur)
                                else
                                    Hashtbl.add inner hash [v]) mapping;
            Hashtbl.add map v mapping

        let create_t n =
            let _ = setup n in
            let gs = create_gs !k !l in
            let tbl = create_tables gs n in
            let map = Hashtbl.create n in
            { hashers = gs ; table = tbl ; map = map }

        let create vectors =
            let n = List.length vectors in
            let t = create_t n in
            List.iter (fun x -> add t x) vectors;
            t

        let query t v =
            let map = t.map in
            let outer = t.table in
            let hashes = Hashtbl.find map v in
            let prepare cur prep =
                List.fold_left
                    (fun x y ->
                        if List.mem y x then x else y::x
                    ) prep cur
            in
            let cc = List.fold_left (fun x (g, hash) ->
                            let inner = Hashtbl.find outer g in
                            let y = Hashtbl.find inner hash in
                            prepare y x) [] hashes
            in
            cc

        let get_all t =
            let create_list_of_vs = fun v _ acc -> v::acc in
            let vs = Hashtbl.fold create_list_of_vs t.map [] in
            List.map (fun v -> (v,query t v)) vs

    end
    :
    sig
        type t
        val create : C.vstore_t list -> t
        val query : t -> C.vstore_t -> C.vstore_t list
        val get_all : t -> (C.vstore_t * C.vstore_t list) list
    end
)

let get_all_classes db =
    let sort_inner pairs =
        List.map (
            fun (v,vs) ->
                (v, List.sort (fun (_,x) (_,y) -> compare x y) vs)
                ) pairs
    in
    (*let remove_dups xs =
        let remove_dup y ys =
            List.filter (fun t -> t<>y) ys
        in
        match xs with
        | l::ls -> l::(remove_dup l ls)
        | [] -> []
    in
    *)
    let cc = List.filter (fun x -> List.length (snd x) > 1) (LshDb.get_all db) in
    sort_inner cc

