open Common

let read_ast_and_annote file =
    print_endline "Parsing...";
    let (pgm, _) = Parse_c.parse_print_error_heuristic file in
    pgm


let _ = read_ast_and_annote "./test.c"
