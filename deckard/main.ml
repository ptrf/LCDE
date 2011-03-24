(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module R = Reader
module C = Context
module Dt = Deckard_types
module Cv = Charv
module P = Process


let testfile = "/Users/ptrf/Dropbox/KU/Datalogi/Bachelorprojekt/work/code/LCDE/deckard/stage1.c"

let parseresult = R.read_file testfile
let parseresult_unpacked = List.map fst parseresult

let resultlol = P.pprogram parseresult_unpacked


