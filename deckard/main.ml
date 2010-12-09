let read_file file =
    let (pgm, _) = Parse_c.parse_c_and_cpp file in
    pgm

let _ = read_file "./test.c"
