(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.mli *)

(* types *)

exception Dimension of string
exception Nofiles of string
exception ImpossiblePos of string

type vstore_t = Charv.charv * Deckard_types.ast_c_anything list
type vseq_t = Charv.charv * Deckard_types.ast_c_anything

(* function definitions *)

(* variable definitions *)

val verbose : bool ref

(* vseq is the sequence of vectors to be considered for merging *)
val vseq : (string * (vseq_t * int)) list ref

(* vstore is a store for all vectors *)
val vstore : vstore_t list ref

(* CONFIGURABILITY *)

(* min token count threshold *)
val tc : int ref

(* LSH initialization variables *)
val r : float ref
val c : float ref

(* file list *)
val files : string ref

(* clone detection within the same file *)
val samefile : bool ref

(* merging properties *)
val stride : int ref
val width : int ref
