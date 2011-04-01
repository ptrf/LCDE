(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module C = Context
module Cv = Charv

let prune_tokencount l =
    List.filter (fun x -> (List.fold_left (+) 0 (fst x)) > !C.tc) l

(* prior to LSH *)
let prune_vstore () =
    C.vstore := prune_tokencount(!C.vstore)

(* after LSH *)
let prune_candidates () =
    ()

    (*
List.fold_left (fun x y -> if List.length y > 1 then y::x else x) [] clones;;
*)
