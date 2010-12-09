(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* context.mli *)

(* types *)

exception Dimension of string

(* function definitions *)

(* cocci composition - maybe redundant here *)
val ( +> ) : 'a -> ('a -> 'b) -> 'b

(* variable definitions *)

val verbose : bool ref

(* vseq is the sequence of vectors to be considered for merging *)
val vseq : Charv.charv list ref

(* vstore is a store for all vectors *)
val vstore : Charv.charv list ref

val dimensions : int
