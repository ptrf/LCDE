(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.ml
 *
 * Contains various context stuff used throughout the implementation of the
 * DECKARD algorithm
 *)

(* Behavioral stuff *)

let verbose = ref false

exception Dimension of string

(* Various function definitions *)

let (+>) o f = f o

(* Global variables and refs *)

let vseq = ref []
let vstore = ref []

(* moved to Deckard_types
let dimensions = 42 *)
