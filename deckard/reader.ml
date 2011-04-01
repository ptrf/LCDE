(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module T = Type_annoter_c
module P = Parse_c

let parse_file file =
    fst (P.parse_c_and_cpp file)

let annotate_pgm pgm =
    T.annotate_program !T.initial_env (List.map fst pgm)

let expand fs =
    List.fold_left (fun l x -> if x <> "" then x::l else l) [] (Str.split (Str.regexp ",[ ]*") fs)

let parse_and_annotate filelist =
    let files = expand filelist in
    List.map (fun x -> annotate_pgm (parse_file x)) files
