(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.ml
 *
 * Contains various context stuff used throughout the implementation of the
 * DECKARD algorithm
 *)

(* types *)
type vstore_t = Charv.charv * Deckard_types.ast_c_anything list
type vseq_t = Charv.charv * Deckard_types.ast_c_anything

(* Behavioral stuff *)

let verbose = ref false

exception Dimension of string
exception Nofiles of string
exception ImpossiblePos of string

(* Various function definitions *)

(* Global variables and refs *)

let vseq = ref []
let vstore = ref []

(* CONFIGURABILITY *)

(* Min token count threshold *)
let tc = ref 10

(* LSH initialization variables *)
let r = ref 10.
let c = ref 1.5

(* file list *)
let files = ref ""

(* clone detection within the same file *)
let samefile = ref false

(* merging properties *)
let stride = ref 3
let width = ref 4
