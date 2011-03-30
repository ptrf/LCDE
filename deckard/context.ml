(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.ml
 *
 * Contains various context stuff used throughout the implementation of the
 * DECKARD algorithm
 *)

(* types *)
type vstore_t = Charv.charv * Deckard_types.ast_c_anything list

(* Behavioral stuff *)

let verbose = ref false

exception Dimension of string

(* Various function definitions *)

let (+>) o f = f o

(* Global variables and refs *)

let vseq = ref []
let vstore = ref []

(* Variables affecting random number generation *)
(* not used
let sigma = 1.
*)

(* LSH initialization variables *)
let r = ref 10.
let c = ref 1.5
