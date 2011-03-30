(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.mli *)

(* types *)

exception Dimension of string

type vstore_t = Charv.charv * Deckard_types.ast_c_anything list

(* function definitions *)

(* cocci composition - maybe redundant here *)
val ( +> ) : 'a -> ('a -> 'b) -> 'b

(* variable definitions *)

val verbose : bool ref

(* vseq is the sequence of vectors to be considered for merging *)
val vseq : (Charv.charv * Deckard_types.ast_c_anything list * int) list ref

(* vstore is a store for all vectors *)
val vstore : (Charv.charv * Deckard_types.ast_c_anything list) list ref

(* Variables affecting random number generation *)
(* unused
val sigma : float
*)

(* LSH initialization variables *)
val r : float ref
val c : float ref

