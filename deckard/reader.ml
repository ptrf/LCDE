(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module T = Type_annoter_c
module P = Parse_c


let parse_file file =
    fst (P.parse_c_and_cpp file)

let annotate_pgm pgm =
    T.annotate_program !T.initial_env (List.map fst pgm)

    (*
let parse_and_annotate_files files =
    let parsed = List.map (fun x -> (x,parse_file x)) files in
    let annotated = List.map (fun (x,y) -> (x, annotate_pgm y)) parsed in
    (parsed,annotated)
    *)

let read_file = (fun x -> annotate_pgm (parse_file x))
