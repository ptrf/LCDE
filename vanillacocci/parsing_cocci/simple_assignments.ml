module Ast0 = Ast0_cocci
module Ast = Ast_cocci
module V0 = Visitor_ast0
module VT0 = Visitor_ast0_types

(* find assignments that can match an initialization *)

let pure_mcodekind = function
    Ast0.CONTEXT(mc) ->
      (match !mc with
	(Ast.NOTHING,_,_) -> true
      |	_ -> false)
  | _ -> false

let is_simple_assign left op =
  (match Ast0.unwrap left with
    Ast0.Ident(_) | Ast0.MetaExpr(_,_,_,_,_) -> true
  | _ -> false)
    &&
  ((Ast0.unwrap_mcode op) = Ast.SimpleAssign)

let is_simple_ast_assign left op minus_left =
  (match Ast.unwrap left with
    Ast.Ident(_) -> true
  | Ast.MetaExpr(name,_,_,_,_,_) ->
      (match Ast0.unwrap minus_left with
	Ast0.MetaExpr(name1,_,_,_,_) ->
	  Ast.unwrap_mcode name = Ast0.unwrap_mcode name1
      |	_ -> false)
  | _ -> false)
    &&
  ((Ast.unwrap_mcode op) = Ast.SimpleAssign)

let warning e msg =
  Common.pr2
    ("the simple assignment expression on line "^
     (string_of_int (Ast0.get_line e))^
     " contains transformations\n"^
     "that prevent it from matching a declaration ("^msg^")\n");
  e

let rebuild e1 left right op simple =
  Ast0.rewrap e1 (Ast0.Assignment(left,op,right,simple))

let rec exp mc e1 =
  match Ast0.unwrap e1 with
    Ast0.Assignment(left,op,right,_) ->
      if is_simple_assign left op
      then
	(if !Flag.sgrep_mode2
	then rebuild e1 left right op true
	else
	  match mc with
	    Ast0.MINUS(mc) ->
	      (match !mc with
		([[Ast.ExpressionTag(e2)]],_) ->
		  (match Ast.unwrap e2 with
		    Ast.Assignment(left',op',_,_) ->
		      if is_simple_ast_assign left' op' left
		      then rebuild e1 left right op true
		      else warning e1 "replacement is not simple"
		  | _ -> warning e1 "replacement is not an assignment")
	      | _ -> warning e1 "multiple replacements")
	  | m ->
	      let pure =
		(pure_mcodekind m) &&
		(pure_mcodekind (Ast0.get_mcodekind left)) &&
		(pure_mcodekind (Ast0.get_mcode_mcodekind op)) in
	      if not pure
	      then warning e1 "not pure"
	      else rebuild e1 left right op pure)
      else e1
  | Ast0.DisjExpr(lp,exps,mids,rp) ->
      Ast0.rewrap e1
	(Ast0.DisjExpr
	   (lp,List.map (function x -> exp (Ast0.get_mcodekind x) x) exps,
	    mids,rp))
  | Ast0.OptExp(e) ->
      Ast0.rewrap e1 (Ast0.OptExp(exp (Ast0.get_mcodekind e) e))
  | Ast0.UniqueExp(e) ->
      Ast0.rewrap e1 (Ast0.UniqueExp(exp (Ast0.get_mcodekind e) e))
  | _ -> e1

let simple_assignments l =
  let statement r k e =
    match Ast0.unwrap e with
      Ast0.Exp(e1) -> Ast0.rewrap e (Ast0.Exp(exp (Ast0.get_mcodekind e) e1))
    | _ -> k e in
  let fn =
    V0.rebuilder
      {V0.rebuilder_functions with VT0.rebuilder_stmtfn = statement} in
  List.map fn.VT0.rebuilder_rec_top_level l
