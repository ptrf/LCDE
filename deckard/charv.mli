(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* Type definitions *)

(* Characteristic vectors are just stored as lists of integers *)
type charv = int list

(* Function definitions *)

(* Create characteristic vector *)
val vcreate : int -> charv

(* Addition of characteristic vectors *)
val ( +: ) : charv -> charv -> charv

(* Get token count of characteristic vector *)
val vtokencount : charv -> int

(* Increment index in characteristic vector *)
val vincr : charv -> int -> charv

(* Get value at index in characteristic vector  *)
val vindex : charv -> int -> int
