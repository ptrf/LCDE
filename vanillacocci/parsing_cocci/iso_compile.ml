module V0 = Visitor_ast0
module VT0 = Visitor_ast0_types
module Ast0 = Ast0_cocci
module Ast = Ast_cocci

(* Detects where position variables can be present in the match of an
isomorpshims.  This is allowed if all elements of an isomorphism have only
one token or if we can somehow match up equal tokens of all of the
isomorphic variants. *)

let sequence_tokens =
  let mcode x =
    (* sort of unpleasant to convert the token representation to a string
       but we can't make a list of mcodes otherwise because the types are all
       different *)
    [(Common.dump (Ast0.unwrap_mcode x),Ast0.get_pos_ref x)] in
  let donothing r k e = k e in
  let bind x y = x @ y in
  let option_default = [] in
  V0.flat_combiner bind option_default
    mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode
    donothing donothing donothing donothing donothing donothing
    donothing donothing
    donothing donothing donothing donothing donothing donothing donothing

(* In general, we will get a list of lists:

[[tokens1;tokens2;tokens3];[tokens4;tokens5;tokens6];[tokens7;tokens8]]

If all of the lists tokens contain only one element, we are done.

Otherwise, we focus on tokens1.  For each of its elements, if they are
present in all of the others, then a position is assigned, and if not then
a position is not.  The order of the elements in the other lists is
irrelevant; we just take the first unannotated element that matches.  Once
we are done with the elements of tokens1, we skip to tokens 4 and repeat,
including considering the one-element special case. *)

let pctr = ref 0
let get_p _ =
  let c = !pctr in
  pctr := c + 1;
  let name = ("",Printf.sprintf "p%d" c) in
  Ast0.MetaPos(Ast0.make_mcode name,[],Ast.PER)

let process_info l =
   let rec loop = function
       [] -> ()
     | ((f::r)::xs) as a ->
	 if List.for_all (List.for_all (function e -> List.length e = 1)) a
	 then
	   let p = get_p() in
	   List.iter (List.iter (List.iter (function (_,pos) -> pos := p))) a
	 else
	   let all = r @ List.concat xs in
	   let rec find_first_available a = function
	       [] -> raise Not_found
	     | (str,pos)::xs ->
		 if str = a && !pos = Ast0.NoMetaPos
		 then pos
		 else find_first_available a xs in
	   List.iter
	     (function (str,pos) ->
	       match !pos with
		 Ast0.NoMetaPos ->
		   (try
		     let entries = List.map (find_first_available str) all in
		     let p = get_p() in
		     pos := p;
		     List.iter (function pos -> pos := p) entries
		   with Not_found -> ())
	       | _ -> (* already have a variable *) ())
	     f;
	   loop xs
     | _ -> failwith "bad iso" in
   loop l

(* Entry point *)

let process (metavars,alts,name) =
  let toks =
    List.map (List.map sequence_tokens.VT0.combiner_rec_anything) alts in
  process_info toks
