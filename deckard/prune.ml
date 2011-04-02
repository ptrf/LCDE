(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module C = Context
module Cv = Charv
module L = Lib_parsing_c
module A = Ast_c
module D = Deckard_types

(*let clones = ref []*)

let prune_tokencount l =
    List.filter (fun x -> (List.fold_left (+) 0 (fst x)) > !C.tc) l


(* prior to LSH *)
let prune_vstore () =
    C.vstore := prune_tokencount(!C.vstore)

(* after LSH *)

let compute_weight cc =
    let get_item i is =
        List.hd (List.filter (fun (x,_) -> x=i) is)
    in
    let rec scc v vs =
        match vs with
        | x::xs -> (if ((x = v) or List.mem v (snd (get_item x cc))) then
                   1 else 0)::(scc v xs)
        | [] -> []
    in
    let rec cu xs =
        match xs with
        | (v,vs)::rem ->
                let n = List.length vs in
                let m = List.fold_left (+) 0 (scc v vs) in
                let u = ( (float_of_int m) /. (float_of_int n) , vs ) in
                u::(cu rem)
        | [] -> []
    in
    cu cc


let get_file_name item =
    let info = (match item with
        | D.Statement s ->
                L.ii_of_stmt s
        | D.Declaration d ->
                L.ii_of_decl d
        | D.Definition d ->
                L.ii_of_toplevel (A.Definition d)
        | D.Cpp_directive d ->
                L.ii_of_toplevel (A.CppTop d)
        | D.Ifdef_directive d ->
                L.ii_of_toplevel (A.IfdefTop d)
        | D.Expression _ -> failwith "Not implemented in prune.ml"
    ) in
    let (filename,_,_,_) = L.lin_col_by_pos info in
    filename


let filter_same_file xs =
    let file_of vs =
        get_file_name (List.hd (snd vs))
    in
    let all_from_same_file (_,vs) =
        let filename = file_of (List.hd vs) in
        (List.length (List.filter (fun x -> (file_of x) <> filename) vs)) <> 0
    in
    List.filter all_from_same_file xs

let get_unique_classes xs =
    let unique_f is i = if List.mem i is then is else i::is in
    List.fold_left unique_f []  xs

    (*
List.fold_left (fun x y -> if List.length y > 1 then y::x else x) [] clones;;
*)
