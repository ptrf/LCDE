(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module R = Reader
module C = Context
module Dt = Deckard_types
module Cv = Charv
module P = Process
module M = Merge

(* TODO make format strings instead :) *)
let speclist =
    Arg.align [
        "-r", Arg.Set_float C.r,
        "[float]   Radius parameter for LSH (default "
        ^ (string_of_float !C.r) ^ ")";
        "-c", Arg.Set_float C.c,
        "[float]   Radius scaling parameter for LSH (default: "
        ^ (string_of_float !C.c) ^ ")";
        "-tc", Arg.Set_int C.tc,
        "[int]   Token count threshold, use to weed out small clones (default: "
        ^ (string_of_int !C.tc) ^ ")";
        "-stride", Arg.Set_int C.stride, "[int]   Window stride in merging phase (default: "
        ^ (string_of_int !C.stride) ^ ")";
        "-width", Arg.Set_int C.width, "[int]   Window width in merging phase (default: "
        ^ (string_of_int !C.width) ^ ")";
        "-samefile", Arg.Set C.samefile, "   Report clones that come from the same file (default: yes)";
        "-files", Arg.Set_string C.files, "[string]   Comma-separated list of filenames to examine";
]


let parse filelist = R.parse_and_annotate filelist

let process fs =
    let parse_results = parse fs in
    let programs = List.map (fun xs -> List.map fst xs) parse_results in
    List.iter (fun toplevels -> P.pprogram toplevels) programs
(*    C.vstore := List.filter (fun x -> (fst x) <> []) !C.vstore *)

let merge () = M.merge ()

let main () =
    Arg.parse speclist (function _ -> ()) "Usage: ";
    if !C.files = "" then
        raise (C.Nofiles "No files given")
    else
        if !C.width < !C.stride then
        print_endline ("[WARNING] The merging window is smaller than the" ^
        " stride! This may lead to weird behaviour, and is not supported.");
        process !C.files;
        merge ()

let _ = main ()

