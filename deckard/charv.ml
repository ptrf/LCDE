(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* Type definitions *)

(* Characteristic vectors are just stored as lists of integers *)
type charv = int list

(* Function definitions *)

(* Create characteristic vector *)
let vcreate index =
    let rec helper i acc =
        if i = 0 then (1::acc)
        else helper (i-1) (0::acc)
    in
    if index < 1 || index > Context.dimensions then
        raise (Failure "No such dimension")
    else List.rev (helper (index-1) [])

(* Addition of characteristic vectors *)

let ( +: ) left right =
    let headorzero v =
        match v with
          x::xs -> (x,xs)
        | [] -> (0,[])
    in
    let rec adder l r acc =
        match l with
          [] -> if r = [] then acc
                else adder r l acc
        | _ -> let (headl,lrest) = headorzero l in
               let (headr,rrest) = headorzero r in
               adder lrest rrest ((headl+headr) :: acc )
    in
    List.rev (adder left right [])



(* Get token count of characteristic vector *)
let vtokencount v =
    List.fold_left ( + ) 0 v

(* Increment index in characteristic vector *)
let vincr v index = (vcreate index) +: v

(* Get value at index in characteristic vector *)
let vindex v index =
    if index < 1 || index > Context.dimensions then
        raise (Failure "No such dimension")
    else
        try
            List.nth v (index-1)
        with Failure _ -> 0