(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)


let read_file file =
    let (parsed, _) = Parse_c.parse_c_and_cpp file in
    parsed


let _ = print_endline (Dumper.dump (read_file "./test.c"))
