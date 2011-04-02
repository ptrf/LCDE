(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module A = Ast_c
module R = Reader
module C = Context
module D = Deckard_types
module Cv = Charv
module P = Process
module M = Merge
module Pr = Prune
module L = Lsh
module Lpc = Lib_parsing_c
module Ppc = Pretty_print_c

(* lshdb *)
let clone_candidates = ref []
let clone_candidates2 = ref []

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

let prune_before () = Pr.prune_vstore ()

let prune_after () =
    let weighted = Pr.compute_weight !clone_candidates in
    clone_candidates2 := Pr.get_unique_classes (if !C.samefile = true then weighted else Pr.filter_same_file weighted)

let lsh () = let lshdb = L.LshDb.create !C.vstore in
             clone_candidates := L.get_all_classes lshdb
(*
            let (file, _, (sl,sc), (el,ec)) = L.ii_of_statement d in
*)

let get_file_info items =
    let get_info item =
        let info = (match item with
        | D.Statement s ->
                Lpc.ii_of_stmt s
        | D.Declaration d ->
                Lpc.ii_of_decl d
        | D.Definition d ->
                Lpc.ii_of_toplevel (A.Definition d)
        | D.Cpp_directive d ->
                Lpc.ii_of_toplevel (A.CppTop d)
        | D.Ifdef_directive d ->
                Lpc.ii_of_toplevel (A.IfdefTop d)
        | D.Expression _ -> failwith "Not implemented in prune.ml"
                ) in
        let (f,_,s,e) = Lpc.lin_col_by_pos info
        in ((s,e),f)
    in
    let (_,f) = get_info (List.hd items) in
    let pos = List.sort compare (List.map get_info items) in
    let s = fst (fst (List.hd pos)) in
    let e = snd (fst (List.hd (List.rev pos))) in
    (f,s,e)

let report_item n =
    (match n with
    | D.Statement s ->
            Ppc.pp_statement_simple s;
            flush_all ()
    | D.Declaration d ->
            Ppc.pp_decl_simple d;
            flush_all ()
    | D.Definition d ->
            Ppc.pp_toplevel_simple (A.Definition d);
            flush_all ()
    | D.Cpp_directive d ->
            Ppc.pp_toplevel_simple (A.CppTop d);
            flush_all ()
    | D.Ifdef_directive d ->
            Ppc.pp_toplevel_simple (A.IfdefTop d);
            flush_all ()
    | D.Expression _ -> failwith "not implemented in main.ml")

let rec print_class vs =
    if vs = [] then failwith "Major problem in main.ml!" else
    let (filename,s,e) = get_file_info vs in
    print_endline ("File: " ^ filename ^ ", lines " ^ (string_of_int (fst s)) ^
    "-" ^ (string_of_int (fst e)) ^ "\n----");
    List.iter report_item vs;
    print_endline "----\n"

let rec print_each_class i classes =
    match classes with
    | (certainty,vs)::rems ->
            print_endline ("Class " ^ (string_of_int i) ^ " weighted at " ^
            (string_of_float (certainty *. 100.)) ^ "%:\n");
            List.iter (fun (_,x) -> print_class x) vs;
            print_each_class (i+1) rems
    | [] -> print_endline "\n============\nEnd of clone class listing"

let report () =
    let num_classes = List.length !clone_candidates2 in
    print_endline ("A total number of " ^ (string_of_int num_classes) ^
    " clone classes were found\n========\n");
    print_each_class 1 !clone_candidates2

let prune_after () =
    let weighted = Pr.compute_weight !clone_candidates in
    clone_candidates2 := Pr.get_unique_classes (if !C.samefile = true then weighted else Pr.filter_same_file weighted)


let main () =
    Arg.parse speclist (function _ -> ()) "Usage: ";
    if !C.files = "" then
        raise (C.Nofiles "No files given")
    else
        if !C.width < !C.stride then
        print_endline ("[WARNING] The merging window is smaller than the" ^
        " stride! This may lead to weird behaviour, and is not supported.");
        process !C.files;
        merge ();
        prune_before ();
        lsh ();
        prune_after ();
        report ()

let _ = main ()
