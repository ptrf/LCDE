# 1 "lexer_cocci.mll"
 
open Parser_cocci_menhir
module D = Data
module Ast = Ast_cocci
module Ast0 = Ast0_cocci
module P = Parse_aux
exception Lexical of string
let tok = Lexing.lexeme

let line = ref 1
let logical_line = ref 0

(* ---------------------------------------------------------------------- *)
(* control codes *)

(* Defined in data.ml
type line_type = MINUS | OPTMINUS | UNIQUEMINUS | PLUS | CONTEXT | UNIQUE | OPT
*)

let current_line_type = ref (D.CONTEXT,!line,!logical_line)

let prev_plus = ref false
let line_start = ref 0 (* offset of the beginning of the line *)
let get_current_line_type lexbuf =
  let (c,l,ll) = !current_line_type in
  let lex_start = Lexing.lexeme_start lexbuf in
  let preceeding_spaces =
    if !line_start < 0 then 0 else lex_start - !line_start in
  (*line_start := -1;*)
  prev_plus := (c = D.PLUS) or (c = D.PLUSPLUS);
  (c,l,ll,lex_start,preceeding_spaces,[],[],Ast0.NoMetaPos)
let current_line_started = ref false
let col_zero = ref true

let reset_line lexbuf =
  line := !line + 1;
  current_line_type := (D.CONTEXT,!line,!logical_line);
  current_line_started := false;
  col_zero := true;
  line_start := Lexing.lexeme_start lexbuf + 1

let started_line = ref (-1)

let start_line seen_char =
  current_line_started := true;
  col_zero := false;
  (if seen_char && not(!line = !started_line)
  then
    begin
      started_line := !line;
      logical_line := !logical_line + 1
    end)

let pass_zero _ = col_zero := false

let lexerr s1 s2 = raise (Lexical (Printf.sprintf "%s%s" s1 s2))

let add_current_line_type x =
  match (x,!current_line_type) with
    (D.MINUS,(D.CONTEXT,ln,lln))  ->
      current_line_type := (D.MINUS,ln,lln)
  | (D.MINUS,(D.UNIQUE,ln,lln))   ->
      current_line_type := (D.UNIQUEMINUS,ln,lln)
  | (D.MINUS,(D.OPT,ln,lln))      ->
      current_line_type := (D.OPTMINUS,ln,lln)
  | (D.PLUS,(D.CONTEXT,ln,lln))   ->
      current_line_type := (D.PLUS,ln,lln)
  | (D.PLUSPLUS,(D.CONTEXT,ln,lln))   ->
      current_line_type := (D.PLUSPLUS,ln,lln)
  | (D.UNIQUE,(D.CONTEXT,ln,lln)) ->
      current_line_type := (D.UNIQUE,ln,lln)
  | (D.OPT,(D.CONTEXT,ln,lln))    ->
      current_line_type := (D.OPT,ln,lln)
  | _ -> lexerr "invalid control character combination" ""

let check_minus_context_linetype s =
  match !current_line_type with
    (D.PLUS,_,_) | (D.PLUSPLUS,_,_) -> lexerr "invalid in a + context: " s
  | _ -> ()

let check_context_linetype s =
  match !current_line_type with
    (D.CONTEXT,_,_) -> ()
  | _ -> lexerr "invalid in a nonempty context: " s

let check_plus_linetype s =
  match !current_line_type with
    (D.PLUS,_,_) | (D.PLUSPLUS,_,_) -> ()
  | _ -> lexerr "invalid in a non + context: " s

let check_arity_context_linetype s =
  match !current_line_type with
    (D.CONTEXT,_,_) | (D.PLUS,_,_) | (D.PLUSPLUS,_,_)
  | (D.UNIQUE,_,_) | (D.OPT,_,_) -> ()
  | _ -> lexerr "invalid in a nonempty context: " s

let check_comment s =
  if not !current_line_started
  then lexerr "+ expected at the beginning of the line" s

let process_include start finish str =
  (match !current_line_type with
    (D.PLUS,_,_) | (D.PLUSPLUS,_,_) ->
      (try
	let _ = Str.search_forward (Str.regexp "\\.\\.\\.") str start in
	lexerr "... not allowed in + include" ""
      with Not_found -> ())
  | _ -> ());
  String.sub str (start + 1) (finish - start - 1)

(* ---------------------------------------------------------------------- *)
type pm = PATCH | MATCH | UNKNOWN

let pm = ref UNKNOWN

let patch_or_match = function
    PATCH ->
      if not !D.ignore_patch_or_match
      then
	(match !pm with
	  MATCH ->
	    lexerr "- or + not allowed in the first column for a match" ""
	| PATCH -> ()
	| UNKNOWN -> Flag.sgrep_mode2 := false; pm := PATCH)
  | MATCH ->
      if not !D.ignore_patch_or_match
      then
	(match !pm with
	  PATCH -> lexerr "* not allowed in the first column for a patch" ""
	| MATCH -> ()
	| UNKNOWN -> Flag.sgrep_mode2 := true; pm := MATCH)
  | _ -> failwith "unexpected argument"

(* ---------------------------------------------------------------------- *)
(* identifiers, including metavariables *)

let metavariables = (Hashtbl.create(100) : (string, D.clt -> token) Hashtbl.t)

let all_metavariables =
  (Hashtbl.create(100) : (string,(string * (D.clt -> token)) list) Hashtbl.t)

let type_names = (Hashtbl.create(100) : (string, D.clt -> token) Hashtbl.t)

let declarer_names = (Hashtbl.create(100) : (string, D.clt -> token) Hashtbl.t)

let iterator_names = (Hashtbl.create(100) : (string, D.clt -> token) Hashtbl.t)

let rule_names = (Hashtbl.create(100) : (string, unit) Hashtbl.t)

let check_var s linetype =
  let fail _ =
    if (!Data.in_prolog || !Data.in_rule_name) &&
      Str.string_match (Str.regexp "<.*>") s 0
    then TPathIsoFile s
    else
      try (Hashtbl.find metavariables s) linetype
      with Not_found ->
	(try (Hashtbl.find type_names s) linetype
	with Not_found ->
	  (try (Hashtbl.find declarer_names s) linetype
	  with Not_found ->
	    (try (Hashtbl.find iterator_names s) linetype
	    with Not_found -> TIdent (s,linetype)))) in
  if !Data.in_meta or !Data.in_rule_name
  then (try Hashtbl.find rule_names s; TRuleName s with Not_found -> fail())
  else fail()

let id_tokens lexbuf =
  let s = tok lexbuf in
  let linetype = get_current_line_type lexbuf in
  let in_rule_name = !Data.in_rule_name in
  let in_meta = !Data.in_meta && not !Data.saw_struct in
  let in_iso = !Data.in_iso in
  let in_prolog = !Data.in_prolog in
  match s with
    "identifier" when in_meta -> check_arity_context_linetype s; TIdentifier
  | "type" when in_meta ->       check_arity_context_linetype s; TType
  | "parameter" when in_meta ->  check_arity_context_linetype s; TParameter
  | "constant"  when in_meta ->  check_arity_context_linetype s; TConstant
  | "generated" when in_rule_name && not (!Flag.make_hrule = None) ->
      check_arity_context_linetype s; TGenerated
  | "expression" when in_meta || in_rule_name ->
      check_arity_context_linetype s; TExpression
  | "declaration" when in_meta || in_rule_name ->
      check_arity_context_linetype s; TDeclaration
  | "field" when in_meta || in_rule_name ->
      check_arity_context_linetype s; TField
  | "initialiser" when in_meta || in_rule_name ->
      check_arity_context_linetype s; TInitialiser
  | "initializer" when in_meta || in_rule_name ->
      check_arity_context_linetype s; TInitialiser
  | "idexpression" when in_meta ->
      check_arity_context_linetype s; TIdExpression
  | "statement" when in_meta ->  check_arity_context_linetype s; TStatement
  | "function"  when in_meta ->  check_arity_context_linetype s; TFunction
  | "local" when in_meta ->      check_arity_context_linetype s; TLocal
  | "list" when in_meta ->       check_arity_context_linetype s; Tlist
  | "fresh" when in_meta ->      check_arity_context_linetype s; TFresh
  | "typedef" when in_meta ->    check_arity_context_linetype s; TTypedef
  | "declarer" when in_meta ->   check_arity_context_linetype s; TDeclarer
  | "iterator" when in_meta ->   check_arity_context_linetype s; TIterator
  | "name" when in_meta ->       check_arity_context_linetype s; TName
  | "position" when in_meta ->   check_arity_context_linetype s; TPosition
  | "any" when in_meta ->        check_arity_context_linetype s; TPosAny
  | "pure" when in_meta && in_iso ->
      check_arity_context_linetype s; TPure
  | "context" when in_meta && in_iso ->
      check_arity_context_linetype s; TContext
  | "error" when in_meta ->      check_arity_context_linetype s; TError
  | "words" when in_meta ->      check_context_linetype s; TWords

  | "using" when in_rule_name || in_prolog ->  check_context_linetype s; TUsing
  | "virtual" when in_prolog or in_rule_name or in_meta ->
      (* don't want to allow virtual as a rule name *)
      check_context_linetype s; TVirtual
  | "disable" when in_rule_name ->  check_context_linetype s; TDisable
  | "extends" when in_rule_name -> check_context_linetype s; TExtends
  | "depends" when in_rule_name -> check_context_linetype s; TDepends
  | "on" when in_rule_name      -> check_context_linetype s; TOn
  | "ever" when in_rule_name    -> check_context_linetype s; TEver
  | "never" when in_rule_name   -> check_context_linetype s; TNever
  (* exists and forall for when are reparsed in parse_cocci.ml *)
  | "exists" when in_rule_name  -> check_context_linetype s; TExists
  | "forall" when in_rule_name  -> check_context_linetype s; TForall
  | "script" when in_rule_name  -> check_context_linetype s; TScript
  | "initialize" when in_rule_name -> check_context_linetype s; TInitialize
  | "finalize" when in_rule_name   -> check_context_linetype s; TFinalize

  | "char" ->       Tchar     linetype
  | "short" ->      Tshort    linetype
  | "int" ->        Tint      linetype
  | "double" ->     Tdouble   linetype
  | "float" ->      Tfloat    linetype
  | "long" ->       Tlong     linetype
  | "void" ->       Tvoid     linetype
  | "size_t" ->     Tsize_t   linetype
  | "ssize_t" ->    Tssize_t  linetype
  | "ptrdiff_t" ->  Tptrdiff_t linetype
  (* in_meta is only for the first keyword; drop it now to allow any type
     name *)
  | "struct" ->     Data.saw_struct := true; Tstruct   linetype
  | "union" ->      Data.saw_struct := true; Tunion    linetype
  | "enum" ->       Data.saw_struct := true; Tenum     linetype
  | "unsigned" ->   Tunsigned linetype
  | "signed" ->     Tsigned   linetype

  | "auto"  ->      Tauto     linetype
  | "register" ->   Tregister linetype
  | "extern" ->     Textern   linetype
  | "static" ->     Tstatic   linetype
  | "inline" ->     Tinline   linetype
  | "typedef" ->    Ttypedef  linetype

  | "const" ->      Tconst    linetype
  | "volatile" ->   Tvolatile linetype

  | "if" ->         TIf       linetype
  | "else" ->       TElse     linetype
  | "while" ->      TWhile    linetype
  | "do" ->         TDo       linetype
  | "for" ->        TFor      linetype
  | "switch" ->     TSwitch   linetype
  | "case" ->       TCase     linetype
  | "default" ->    TDefault  linetype
  | "return" ->     TReturn   linetype
  | "break" ->      TBreak    linetype
  | "continue" ->   TContinue linetype
  | "goto" ->       TGoto     linetype

  | "sizeof" ->     TSizeof   linetype

  | "Expression"       when !Data.in_iso -> TIsoExpression
  | "ArgExpression"    when !Data.in_iso -> TIsoArgExpression
  | "TestExpression"   when !Data.in_iso -> TIsoTestExpression
  | "ToTestExpression" when !Data.in_iso -> TIsoToTestExpression
  | "Statement"        when !Data.in_iso -> TIsoStatement
  | "Declaration"      when !Data.in_iso -> TIsoDeclaration
  | "Type"             when !Data.in_iso -> TIsoType
  | "TopLevel"         when !Data.in_iso -> TIsoTopLevel

  | "_" when !Data.in_meta -> TUnderscore

  | s -> check_var s linetype

let mkassign op lexbuf =
  TAssign (Ast.OpAssign op, (get_current_line_type lexbuf))

let init _ =
  line := 1;
  logical_line := 0;
  prev_plus := false;
  line_start := 0;
  current_line_started := false;
  current_line_type := (D.CONTEXT,0,0);
  col_zero := true;
  pm := UNKNOWN;
  Data.in_rule_name := false;
  Data.in_meta := false;
  Data.in_prolog := false;
  Data.saw_struct := false;
  Data.inheritable_positions := [];
  Hashtbl.clear all_metavariables;
  Hashtbl.clear Data.all_metadecls;
  Hashtbl.clear metavariables;
  Hashtbl.clear type_names;
  Hashtbl.clear rule_names;
  Hashtbl.clear iterator_names;
  Hashtbl.clear declarer_names;
  let get_name (_,x) = x in
  Data.add_id_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaId(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_virt_id_meta_found :=
    (fun name vl ->
      let fn clt = TIdent(vl,clt) in
      Hashtbl.replace metavariables name fn);
  Data.add_virt_id_meta_not_found :=
    (fun name pure ->
      let fn clt = TMetaId(name,Ast.IdNoConstraint,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_fresh_id_meta :=
    (fun name ->
      let fn clt = TMetaId(name,Ast.IdNoConstraint,Ast0.Impure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_type_meta :=
    (fun name pure ->
      let fn clt = TMetaType(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_init_meta :=
    (fun name pure ->
      let fn clt = TMetaInit(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_param_meta :=
    (function name -> function pure ->
      let fn clt = TMetaParam(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_paramlist_meta :=
    (function name -> function lenname -> function pure ->
      let fn clt = TMetaParamList(name,lenname,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_const_meta :=
    (fun tyopt name constraints pure ->
      let fn clt = TMetaConst(name,constraints,pure,tyopt,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_err_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaErr(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_exp_meta :=
    (fun tyopt name constraints pure ->
      let fn clt = TMetaExp(name,constraints,pure,tyopt,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_idexp_meta :=
    (fun tyopt name constraints pure ->
      let fn clt = TMetaIdExp(name,constraints,pure,tyopt,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_local_idexp_meta :=
    (fun tyopt name constraints pure ->
      let fn clt = TMetaLocalIdExp(name,constraints,pure,tyopt,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_explist_meta :=
    (function name -> function lenname -> function pure ->
      let fn clt = TMetaExpList(name,lenname,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_decl_meta :=
    (function name -> function pure ->
      let fn clt = TMetaDecl(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_field_meta :=
    (function name -> function pure ->
      let fn clt = TMetaField(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_stm_meta :=
    (function name -> function pure ->
      let fn clt = TMetaStm(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_stmlist_meta :=
    (function name -> function pure ->
      let fn clt = TMetaStmList(name,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_func_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaFunc(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_local_func_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaLocalFunc(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_iterator_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaIterator(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_declarer_meta :=
    (fun name constraints pure ->
      let fn clt = TMetaDeclarer(name,constraints,pure,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_pos_meta :=
    (fun name constraints any ->
      let fn ((d,ln,_,_,_,_,_,_) as clt) =
	(if d = Data.PLUS
	then
	  failwith
	    (Printf.sprintf "%d: positions only allowed in minus code" ln));
	TMetaPos(name,constraints,any,clt) in
      Hashtbl.replace metavariables (get_name name) fn);
  Data.add_type_name :=
    (function name ->
      let fn clt = TTypeId(name,clt) in
      Hashtbl.replace type_names name fn);
  Data.add_declarer_name :=
    (function name ->
      let fn clt = TDeclarerId(name,clt) in
      Hashtbl.replace declarer_names name fn);
  Data.add_iterator_name :=
    (function name ->
      let fn clt = TIteratorId(name,clt) in
      Hashtbl.replace iterator_names name fn);
  Data.init_rule := (function _ -> Hashtbl.clear metavariables);
  Data.install_bindings :=
    (function parent ->
      List.iter (function (name,fn) -> Hashtbl.add metavariables name fn)
	(Hashtbl.find all_metavariables parent))

(* the following is needed to properly tokenize include files.  Because an
include file is included after seeing a @, so current_line_started is true.
Current_line_started is not important for parsing the name of a rule, so we
don't have to reset this value to true after parsing an included file. *)
let include_init _ =
  current_line_started := false

let drop_spaces s =
  let len = String.length s in
  let rec loop n =
    if n = len
    then n
    else
      if List.mem (String.get s n) [' ';'\t']
      then loop (n+1)
      else n in
  let start = loop 0 in
  String.sub s start (len - start)

# 446 "lexer_cocci.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\177\255\178\255\081\000\119\000\183\255\184\255\192\000\
    \183\000\207\255\078\000\035\000\090\000\080\000\082\000\083\000\
    \225\255\226\255\229\255\230\255\231\255\232\255\234\255\084\000\
    \106\000\238\255\240\255\116\000\117\000\140\000\013\001\023\001\
    \098\001\087\000\088\000\088\000\138\000\255\255\222\000\188\255\
    \214\255\192\000\252\255\250\255\205\255\092\000\249\255\173\001\
    \248\001\067\002\142\002\217\002\036\003\108\000\141\000\093\000\
    \245\255\243\255\058\003\068\003\078\003\094\000\097\000\114\000\
    \115\000\117\000\246\255\118\000\135\000\244\255\209\255\180\255\
    \217\255\142\000\228\255\050\001\216\255\147\000\148\002\233\255\
    \235\255\237\255\199\255\211\255\215\255\213\255\179\255\206\255\
    \200\255\212\255\210\255\204\255\130\000\208\255\102\000\095\000\
    \092\000\127\003\194\255\092\000\091\000\096\000\108\000\205\000\
    \136\003\219\003\192\255\086\003\112\000\109\000\102\000\121\000\
    \121\000\129\003\161\000\190\000\191\000\191\255\189\000\190\255\
    \149\002\087\003\089\003\090\003\150\002\092\003\159\003\151\002\
    \112\000\128\000\245\002\127\000\137\000\153\002\191\002\145\000\
    \150\000\194\002\142\000\141\000\195\002\067\003\006\001\045\004\
    \068\004\122\004\134\004\156\004\078\004\100\004\226\004\007\001\
    \181\255\194\000\246\000\194\004\042\001\040\005\128\003\045\001\
    \252\255\254\255\217\004\046\001\063\005\253\255\047\001\255\255\
    \105\003\254\255\166\004\255\255\251\255\102\005\144\004\255\004\
    \253\255\157\005\252\255\010\003\252\255\253\255\254\255\040\001\
    \255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\074\000\074\000\255\255\255\255\070\000\
    \078\000\255\255\054\000\060\000\059\000\037\000\033\000\031\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\019\000\
    \078\000\255\255\255\255\014\000\013\000\053\000\028\000\070\000\
    \070\000\016\000\034\000\004\000\032\000\255\255\001\000\255\255\
    \255\255\002\000\255\255\255\255\255\255\255\255\255\255\070\000\
    \070\000\007\000\070\000\070\000\073\000\255\255\008\000\255\255\
    \255\255\255\255\255\255\073\000\255\255\052\000\058\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\036\000\255\255\068\000\255\255\035\000\069\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\057\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\062\000\255\255\066\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \066\000\066\000\066\000\066\000\066\000\066\000\066\000\066\000\
    \255\255\255\255\255\255\255\255\255\255\066\000\066\000\255\255\
    \255\255\066\000\255\255\255\255\066\000\074\000\074\000\255\255\
    \073\000\255\255\255\255\074\000\073\000\255\255\074\000\074\000\
    \255\255\255\255\004\000\004\000\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\001\000\255\255\255\255\004\000\002\000\002\000\
    \255\255\003\000\255\255\255\255\255\255\255\255\255\255\004\000\
    \255\255";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\255\255\255\255\000\000\000\000\255\255\
    \255\255\000\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\000\000\
    \000\000\041\000\000\000\000\000\000\000\255\255\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\000\000\000\000\000\000\
    \000\000\255\255\000\000\075\000\000\000\255\255\078\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\120\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\118\000\116\000\116\000\000\000\118\000\000\000\
    \120\000\120\000\120\000\120\000\124\000\120\000\120\000\127\000\
    \255\255\255\255\255\255\255\255\255\255\133\000\134\000\255\255\
    \255\255\137\000\255\255\255\255\140\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\154\000\255\255\156\000\255\255\255\255\255\255\255\255\
    \000\000\000\000\255\255\255\255\255\255\000\000\255\255\000\000\
    \169\000\000\000\172\000\000\000\000\000\255\255\255\255\255\255\
    \000\000\255\255\000\000\180\000\000\000\000\000\000\000\255\255\
    \000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\038\000\037\000\037\000\037\000\037\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \038\000\033\000\005\000\008\000\000\000\014\000\012\000\006\000\
    \025\000\022\000\015\000\027\000\017\000\028\000\030\000\036\000\
    \004\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\009\000\016\000\029\000\013\000\010\000\026\000\
    \035\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\032\000\
    \007\000\007\000\007\000\021\000\024\000\020\000\011\000\007\000\
    \090\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\031\000\
    \007\000\007\000\007\000\019\000\023\000\018\000\034\000\144\000\
    \088\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\091\000\092\000\087\000\086\000\085\000\
    \084\000\083\000\081\000\079\000\044\000\043\000\145\000\089\000\
    \042\000\046\000\054\000\057\000\071\000\141\000\070\000\077\000\
    \067\000\065\000\073\000\066\000\068\000\144\000\142\000\147\000\
    \147\000\147\000\147\000\147\000\147\000\147\000\147\000\146\000\
    \146\000\076\000\072\000\074\000\039\000\069\000\145\000\063\000\
    \055\000\041\000\064\000\075\000\145\000\141\000\078\000\093\000\
    \097\000\099\000\100\000\141\000\101\000\107\000\142\000\040\000\
    \062\000\061\000\255\255\056\000\142\000\108\000\102\000\143\000\
    \082\000\103\000\130\000\109\000\129\000\045\000\104\000\097\000\
    \128\000\110\000\098\000\111\000\145\000\112\000\113\000\255\255\
    \255\255\117\000\138\000\141\000\135\000\134\000\080\000\038\000\
    \037\000\037\000\037\000\037\000\142\000\104\000\133\000\143\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\136\000\119\000\137\000\139\000\038\000\140\000\
    \002\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\096\000\094\000\167\000\155\000\007\000\
    \095\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\053\000\255\255\052\000\052\000\052\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\052\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\160\000\151\000\152\000\160\000\161\000\165\000\184\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\151\000\152\000\000\000\000\000\007\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\050\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\047\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\255\255\255\255\255\255\
    \255\255\007\000\255\255\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\007\000\007\000\
    \007\000\007\000\048\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \000\000\000\000\000\000\000\000\007\000\000\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\255\255\000\000\000\000\000\000\000\000\000\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\049\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\000\000\000\000\000\000\000\000\007\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\255\255\255\255\
    \255\255\255\255\007\000\255\255\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \000\000\255\255\000\000\000\000\255\255\255\255\000\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\000\000\000\000\000\000\000\000\007\000\000\000\007\000\
    \007\000\007\000\007\000\051\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\000\000\182\000\182\000\182\000\182\000\
    \000\000\000\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\183\000\181\000\000\000\000\000\
    \007\000\000\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\049\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\052\000\052\000\052\000\052\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\131\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\060\000\255\255\060\000\
    \132\000\058\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \097\000\058\000\113\000\171\000\000\000\000\000\000\000\152\000\
    \000\000\104\000\000\000\000\000\255\255\255\255\255\255\255\255\
    \152\000\255\255\000\000\000\000\000\000\000\000\000\000\097\000\
    \000\000\113\000\000\000\115\000\000\000\000\000\000\000\161\000\
    \104\000\255\255\000\000\000\000\000\000\000\000\000\000\152\000\
    \162\000\162\000\162\000\162\000\162\000\162\000\162\000\162\000\
    \152\000\000\000\122\000\125\000\000\000\114\000\123\000\255\255\
    \124\000\126\000\255\255\255\255\121\000\170\000\000\000\000\000\
    \000\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\096\000\094\000\000\000\000\000\105\000\
    \095\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\106\000\000\000\127\000\000\000\000\000\
    \000\000\000\000\255\255\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\000\000\000\000\
    \000\000\000\000\105\000\000\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\255\255\255\255\
    \000\000\255\255\255\255\000\000\255\255\150\000\150\000\150\000\
    \150\000\150\000\150\000\150\000\150\000\150\000\150\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\150\000\150\000\
    \150\000\150\000\150\000\150\000\144\000\144\000\144\000\144\000\
    \144\000\144\000\144\000\144\000\144\000\144\000\148\000\148\000\
    \148\000\148\000\148\000\148\000\148\000\148\000\148\000\148\000\
    \000\000\058\000\000\000\000\000\000\000\000\000\150\000\150\000\
    \150\000\150\000\150\000\150\000\148\000\148\000\148\000\148\000\
    \148\000\148\000\148\000\148\000\148\000\148\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\149\000\000\000\149\000\
    \000\000\058\000\148\000\148\000\148\000\148\000\148\000\148\000\
    \148\000\148\000\148\000\148\000\144\000\000\000\146\000\146\000\
    \146\000\146\000\146\000\146\000\146\000\146\000\146\000\146\000\
    \175\000\175\000\175\000\175\000\175\000\175\000\175\000\175\000\
    \000\000\000\000\144\000\145\000\147\000\147\000\147\000\147\000\
    \147\000\147\000\147\000\147\000\146\000\146\000\174\000\174\000\
    \174\000\174\000\174\000\174\000\174\000\174\000\000\000\000\000\
    \000\000\145\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \141\000\159\000\000\000\145\000\000\000\000\000\000\000\000\000\
    \000\000\142\000\158\000\158\000\158\000\158\000\158\000\158\000\
    \158\000\158\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \161\000\145\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \141\000\163\000\163\000\163\000\163\000\163\000\163\000\163\000\
    \163\000\142\000\150\000\150\000\150\000\150\000\150\000\150\000\
    \150\000\150\000\150\000\150\000\000\000\000\000\173\000\000\000\
    \000\000\000\000\000\000\150\000\150\000\150\000\150\000\150\000\
    \150\000\000\000\000\000\000\000\000\000\000\000\141\000\176\000\
    \176\000\176\000\176\000\176\000\176\000\176\000\176\000\142\000\
    \000\000\000\000\157\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\150\000\150\000\150\000\150\000\150\000\
    \150\000\000\000\000\000\000\000\000\000\000\000\141\000\160\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\142\000\
    \164\000\164\000\164\000\164\000\164\000\164\000\164\000\164\000\
    \164\000\164\000\000\000\000\000\000\000\000\000\165\000\000\000\
    \000\000\164\000\164\000\164\000\164\000\164\000\164\000\166\000\
    \166\000\166\000\166\000\166\000\166\000\166\000\166\000\166\000\
    \166\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \166\000\166\000\166\000\166\000\166\000\166\000\000\000\000\000\
    \000\000\164\000\164\000\164\000\164\000\164\000\164\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\177\000\177\000\
    \177\000\177\000\177\000\177\000\177\000\177\000\177\000\177\000\
    \166\000\166\000\166\000\166\000\166\000\166\000\255\255\177\000\
    \177\000\177\000\177\000\177\000\177\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\000\000\177\000\
    \177\000\177\000\177\000\177\000\177\000\178\000\178\000\178\000\
    \178\000\178\000\178\000\178\000\178\000\178\000\178\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\178\000\178\000\
    \178\000\178\000\178\000\178\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\178\000\178\000\
    \178\000\178\000\178\000\178\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \011\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
    \012\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\010\000\010\000\013\000\013\000\014\000\
    \015\000\023\000\024\000\024\000\033\000\034\000\003\000\012\000\
    \035\000\045\000\053\000\055\000\061\000\003\000\062\000\027\000\
    \063\000\064\000\028\000\065\000\067\000\004\000\003\000\004\000\
    \004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
    \004\000\027\000\028\000\028\000\036\000\068\000\003\000\029\000\
    \054\000\036\000\029\000\073\000\004\000\003\000\077\000\092\000\
    \008\000\096\000\099\000\004\000\100\000\095\000\003\000\036\000\
    \029\000\029\000\041\000\054\000\004\000\095\000\101\000\004\000\
    \023\000\102\000\094\000\108\000\094\000\033\000\103\000\008\000\
    \094\000\109\000\008\000\110\000\004\000\111\000\112\000\114\000\
    \115\000\116\000\128\000\004\000\129\000\131\000\024\000\038\000\
    \038\000\038\000\038\000\038\000\004\000\103\000\132\000\004\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\135\000\118\000\136\000\138\000\038\000\139\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\008\000\008\000\154\000\153\000\007\000\
    \008\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\030\000\075\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\156\000\142\000\151\000\159\000\163\000\166\000\183\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\142\000\151\000\255\255\255\255\031\000\255\255\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\255\255\255\255\255\255\255\255\
    \255\255\114\000\255\255\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\118\000\115\000\116\000\
    \041\000\032\000\153\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \255\255\255\255\255\255\255\255\047\000\255\255\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\075\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\255\255\255\255\255\255\255\255\048\000\
    \255\255\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
    \048\000\048\000\048\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\078\000\120\000\
    \124\000\127\000\049\000\133\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \255\255\134\000\255\255\255\255\137\000\140\000\255\255\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\255\255\255\255\255\255\255\255\050\000\255\255\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
    \050\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\255\255\179\000\179\000\179\000\179\000\
    \255\255\255\255\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\179\000\179\000\255\255\255\255\
    \051\000\255\255\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\052\000\052\000\052\000\052\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\130\000\255\255\
    \107\000\121\000\255\255\122\000\123\000\058\000\125\000\058\000\
    \130\000\052\000\058\000\058\000\058\000\058\000\058\000\058\000\
    \058\000\058\000\058\000\058\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\060\000\060\000\
    \060\000\060\000\060\000\060\000\060\000\060\000\060\000\060\000\
    \097\000\052\000\113\000\168\000\255\255\255\255\255\255\141\000\
    \255\255\104\000\255\255\255\255\078\000\120\000\124\000\127\000\
    \141\000\133\000\255\255\255\255\255\255\255\255\255\255\097\000\
    \255\255\113\000\255\255\113\000\255\255\255\255\255\255\158\000\
    \104\000\126\000\255\255\255\255\255\255\255\255\255\255\141\000\
    \158\000\158\000\158\000\158\000\158\000\158\000\158\000\158\000\
    \141\000\255\255\107\000\121\000\255\255\113\000\122\000\134\000\
    \123\000\125\000\137\000\140\000\107\000\168\000\255\255\255\255\
    \255\255\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\097\000\097\000\255\255\255\255\104\000\
    \097\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
    \104\000\104\000\104\000\105\000\255\255\126\000\255\255\255\255\
    \255\255\255\255\179\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\255\255\255\255\
    \255\255\255\255\105\000\255\255\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\105\000\105\000\
    \105\000\105\000\105\000\105\000\105\000\105\000\107\000\121\000\
    \255\255\122\000\123\000\255\255\125\000\143\000\143\000\143\000\
    \143\000\143\000\143\000\143\000\143\000\143\000\143\000\255\255\
    \255\255\168\000\255\255\255\255\255\255\255\255\143\000\143\000\
    \143\000\143\000\143\000\143\000\144\000\144\000\144\000\144\000\
    \144\000\144\000\144\000\144\000\144\000\144\000\148\000\148\000\
    \148\000\148\000\148\000\148\000\148\000\148\000\148\000\148\000\
    \255\255\144\000\255\255\255\255\255\255\255\255\143\000\143\000\
    \143\000\143\000\143\000\143\000\149\000\149\000\149\000\149\000\
    \149\000\149\000\149\000\149\000\149\000\149\000\255\255\126\000\
    \255\255\255\255\255\255\255\255\255\255\145\000\255\255\145\000\
    \255\255\144\000\145\000\145\000\145\000\145\000\145\000\145\000\
    \145\000\145\000\145\000\145\000\146\000\255\255\146\000\146\000\
    \146\000\146\000\146\000\146\000\146\000\146\000\146\000\146\000\
    \174\000\174\000\174\000\174\000\174\000\174\000\174\000\174\000\
    \255\255\255\255\147\000\146\000\147\000\147\000\147\000\147\000\
    \147\000\147\000\147\000\147\000\147\000\147\000\170\000\170\000\
    \170\000\170\000\170\000\170\000\170\000\170\000\255\255\255\255\
    \255\255\147\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \147\000\155\000\255\255\146\000\255\255\255\255\255\255\255\255\
    \255\255\147\000\155\000\155\000\155\000\155\000\155\000\155\000\
    \155\000\155\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \162\000\147\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \147\000\162\000\162\000\162\000\162\000\162\000\162\000\162\000\
    \162\000\147\000\150\000\150\000\150\000\150\000\150\000\150\000\
    \150\000\150\000\150\000\150\000\255\255\255\255\170\000\255\255\
    \255\255\255\255\255\255\150\000\150\000\150\000\150\000\150\000\
    \150\000\255\255\255\255\255\255\255\255\255\255\150\000\175\000\
    \175\000\175\000\175\000\175\000\175\000\175\000\175\000\150\000\
    \255\255\255\255\155\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\150\000\150\000\150\000\150\000\150\000\
    \150\000\255\255\255\255\255\255\255\255\255\255\150\000\157\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\150\000\
    \157\000\157\000\157\000\157\000\157\000\157\000\157\000\157\000\
    \157\000\157\000\255\255\255\255\255\255\255\255\164\000\255\255\
    \255\255\157\000\157\000\157\000\157\000\157\000\157\000\164\000\
    \164\000\164\000\164\000\164\000\164\000\164\000\164\000\164\000\
    \164\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \164\000\164\000\164\000\164\000\164\000\164\000\255\255\255\255\
    \255\255\157\000\157\000\157\000\157\000\157\000\157\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\173\000\173\000\
    \173\000\173\000\173\000\173\000\173\000\173\000\173\000\173\000\
    \164\000\164\000\164\000\164\000\164\000\164\000\170\000\173\000\
    \173\000\173\000\173\000\173\000\173\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\155\000\255\255\255\255\255\255\255\255\173\000\
    \173\000\173\000\173\000\173\000\173\000\177\000\177\000\177\000\
    \177\000\177\000\177\000\177\000\177\000\177\000\177\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\177\000\177\000\
    \177\000\177\000\177\000\177\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\177\000\177\000\
    \177\000\177\000\177\000\177\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\000\000\009\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_backtrk_code = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_default_code = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_trans_code = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\001\000\001\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000";
  Lexing.lex_check_code = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\103\000\104\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \103\000\104\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_code = 
   "\255\002\255\001\255\255\000\001\255\000\002\255";
}

let rec token lexbuf =
lexbuf.Lexing.lex_mem <- Array.create 3 (-1) ;   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.new_engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 468 "lexer_cocci.mll"
    ( let cls = !current_line_started in
      
      if not cls
      then
	begin
	  match !current_line_type with
	    (D.PLUS,_,_) | (D.PLUSPLUS,_,_) ->
	      let info = get_current_line_type lexbuf in
	      reset_line lexbuf;
	      TPragma (Ast.Noindent "", info)
	  | _ -> reset_line lexbuf; token lexbuf
	end
      else (reset_line lexbuf; token lexbuf) )
# 1115 "lexer_cocci.ml"

  | 1 ->
# 482 "lexer_cocci.mll"
                   ( start_line false; token lexbuf )
# 1120 "lexer_cocci.ml"

  | 2 ->
# 484 "lexer_cocci.mll"
                   (
    match !current_line_type with
      (D.PLUS,_,_) | (D.PLUSPLUS,_,_) ->
	TPragma (Ast.Indent (tok lexbuf), get_current_line_type lexbuf)
    | _ -> start_line false; token lexbuf )
# 1129 "lexer_cocci.ml"

  | 3 ->
# 490 "lexer_cocci.mll"
         ( start_line true; TArobArob )
# 1134 "lexer_cocci.ml"

  | 4 ->
# 491 "lexer_cocci.mll"
         ( pass_zero();
	   if !Data.in_rule_name or not !current_line_started
	   then (start_line true; TArob)
	   else (check_minus_context_linetype "@"; TPArob) )
# 1142 "lexer_cocci.ml"

  | 5 ->
# 496 "lexer_cocci.mll"
          ( start_line true; TTildeEq (get_current_line_type lexbuf) )
# 1147 "lexer_cocci.ml"

  | 6 ->
# 497 "lexer_cocci.mll"
          ( start_line true; TTildeExclEq (get_current_line_type lexbuf) )
# 1152 "lexer_cocci.ml"

  | 7 ->
# 499 "lexer_cocci.mll"
      ( start_line true; check_minus_context_linetype (tok lexbuf);
	TWhen (get_current_line_type lexbuf) )
# 1158 "lexer_cocci.ml"

  | 8 ->
# 503 "lexer_cocci.mll"
      ( start_line true; check_minus_context_linetype (tok lexbuf);
	TEllipsis (get_current_line_type lexbuf) )
# 1164 "lexer_cocci.ml"

  | 9 ->
# 514 "lexer_cocci.mll"
           ( start_line true; check_context_linetype (tok lexbuf);
	     TOEllipsis (get_current_line_type lexbuf) )
# 1170 "lexer_cocci.ml"

  | 10 ->
# 516 "lexer_cocci.mll"
           ( start_line true; check_context_linetype (tok lexbuf);
	     TCEllipsis (get_current_line_type lexbuf) )
# 1176 "lexer_cocci.ml"

  | 11 ->
# 518 "lexer_cocci.mll"
            ( start_line true; check_minus_context_linetype (tok lexbuf);
	     TPOEllipsis (get_current_line_type lexbuf) )
# 1182 "lexer_cocci.ml"

  | 12 ->
# 520 "lexer_cocci.mll"
            ( start_line true; check_minus_context_linetype (tok lexbuf);
	     TPCEllipsis (get_current_line_type lexbuf) )
# 1188 "lexer_cocci.ml"

  | 13 ->
# 533 "lexer_cocci.mll"
        ( pass_zero();
	  if !current_line_started
	  then (start_line true; TMinus (get_current_line_type lexbuf))
          else (patch_or_match PATCH;
		add_current_line_type D.MINUS; token lexbuf) )
# 1197 "lexer_cocci.ml"

  | 14 ->
# 538 "lexer_cocci.mll"
        ( pass_zero();
	  if !current_line_started
	  then (start_line true; TPlus (get_current_line_type lexbuf))
          else if !Data.in_meta
	  then TPlus0
          else (patch_or_match PATCH;
		add_current_line_type D.PLUS; token lexbuf) )
# 1208 "lexer_cocci.ml"

  | 15 ->
# 545 "lexer_cocci.mll"
        ( pass_zero();
	  if !current_line_started
	  then (start_line true; TWhy (get_current_line_type lexbuf))
          else if !Data.in_meta
	  then TWhy0
          else (add_current_line_type D.OPT; token lexbuf) )
# 1218 "lexer_cocci.ml"

  | 16 ->
# 551 "lexer_cocci.mll"
        ( pass_zero();
	  if !current_line_started
	  then (start_line true; TBang (get_current_line_type lexbuf))
          else if !Data.in_meta
	  then TBang0
          else (add_current_line_type D.UNIQUE; token lexbuf) )
# 1228 "lexer_cocci.ml"

  | 17 ->
# 557 "lexer_cocci.mll"
        ( if !Data.in_meta or not !col_zero
	  then (start_line true; TOPar (get_current_line_type lexbuf))
          else
            (start_line true; check_context_linetype (tok lexbuf);
	     TOPar0 (get_current_line_type lexbuf)))
# 1237 "lexer_cocci.ml"

  | 18 ->
# 562 "lexer_cocci.mll"
          ( start_line true; TOPar0 (get_current_line_type lexbuf) )
# 1242 "lexer_cocci.ml"

  | 19 ->
# 563 "lexer_cocci.mll"
        ( if not (!col_zero)
	  then (start_line true; TOr(get_current_line_type lexbuf))
          else (start_line true;
		check_context_linetype (tok lexbuf);
		TMid0 (get_current_line_type lexbuf)))
# 1251 "lexer_cocci.ml"

  | 20 ->
# 568 "lexer_cocci.mll"
          ( start_line true; TMid0 (get_current_line_type lexbuf) )
# 1256 "lexer_cocci.ml"

  | 21 ->
# 569 "lexer_cocci.mll"
        ( if not !col_zero
	  then (start_line true; TCPar (get_current_line_type lexbuf))
          else
            (start_line true; check_context_linetype (tok lexbuf);
	     TCPar0 (get_current_line_type lexbuf)))
# 1265 "lexer_cocci.ml"

  | 22 ->
# 574 "lexer_cocci.mll"
          ( start_line true; TCPar0 (get_current_line_type lexbuf) )
# 1270 "lexer_cocci.ml"

  | 23 ->
# 576 "lexer_cocci.mll"
        ( start_line true; TOCro (get_current_line_type lexbuf)   )
# 1275 "lexer_cocci.ml"

  | 24 ->
# 577 "lexer_cocci.mll"
        ( start_line true; TCCro (get_current_line_type lexbuf)   )
# 1280 "lexer_cocci.ml"

  | 25 ->
# 578 "lexer_cocci.mll"
        ( start_line true; TOBrace (get_current_line_type lexbuf) )
# 1285 "lexer_cocci.ml"

  | 26 ->
# 579 "lexer_cocci.mll"
        ( start_line true; TCBrace (get_current_line_type lexbuf) )
# 1290 "lexer_cocci.ml"

  | 27 ->
# 581 "lexer_cocci.mll"
                   ( start_line true; TPtrOp (get_current_line_type lexbuf)  )
# 1295 "lexer_cocci.ml"

  | 28 ->
# 582 "lexer_cocci.mll"
                   ( start_line true; TDot (get_current_line_type lexbuf)    )
# 1300 "lexer_cocci.ml"

  | 29 ->
# 583 "lexer_cocci.mll"
                   ( start_line true; TComma (get_current_line_type lexbuf)  )
# 1305 "lexer_cocci.ml"

  | 30 ->
# 584 "lexer_cocci.mll"
                   ( start_line true;
		     if !Data.in_meta
		     then TMPtVirg (* works better with tokens_all *)
		     else TPtVirg (get_current_line_type lexbuf) )
# 1313 "lexer_cocci.ml"

  | 31 ->
# 590 "lexer_cocci.mll"
                   ( pass_zero();
		     if !current_line_started
		     then
		       (start_line true; TMul (get_current_line_type lexbuf))
		     else
		       (patch_or_match MATCH;
			add_current_line_type D.MINUS; token lexbuf) )
# 1324 "lexer_cocci.ml"

  | 32 ->
# 597 "lexer_cocci.mll"
                   ( start_line true;
		     TDmOp (Ast.Div,get_current_line_type lexbuf) )
# 1330 "lexer_cocci.ml"

  | 33 ->
# 599 "lexer_cocci.mll"
                   ( start_line true;
		     TDmOp (Ast.Mod,get_current_line_type lexbuf) )
# 1336 "lexer_cocci.ml"

  | 34 ->
# 601 "lexer_cocci.mll"
                   ( start_line true;  TTilde (get_current_line_type lexbuf) )
# 1341 "lexer_cocci.ml"

  | 35 ->
# 603 "lexer_cocci.mll"
                   ( pass_zero();
 		     if !current_line_started
 		     then
 		       (start_line true; TInc (get_current_line_type lexbuf))
 		     else (patch_or_match PATCH;
 			   add_current_line_type D.PLUSPLUS; token lexbuf) )
# 1351 "lexer_cocci.ml"

  | 36 ->
# 609 "lexer_cocci.mll"
                   ( start_line true;  TDec (get_current_line_type lexbuf) )
# 1356 "lexer_cocci.ml"

  | 37 ->
# 611 "lexer_cocci.mll"
                   ( start_line true; TEq (get_current_line_type lexbuf) )
# 1361 "lexer_cocci.ml"

  | 38 ->
# 613 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Minus lexbuf )
# 1366 "lexer_cocci.ml"

  | 39 ->
# 614 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Plus lexbuf )
# 1371 "lexer_cocci.ml"

  | 40 ->
# 616 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Mul lexbuf )
# 1376 "lexer_cocci.ml"

  | 41 ->
# 617 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Div lexbuf )
# 1381 "lexer_cocci.ml"

  | 42 ->
# 618 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Mod lexbuf )
# 1386 "lexer_cocci.ml"

  | 43 ->
# 620 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.And lexbuf )
# 1391 "lexer_cocci.ml"

  | 44 ->
# 621 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Or lexbuf )
# 1396 "lexer_cocci.ml"

  | 45 ->
# 622 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.Xor lexbuf )
# 1401 "lexer_cocci.ml"

  | 46 ->
# 624 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.DecLeft lexbuf )
# 1406 "lexer_cocci.ml"

  | 47 ->
# 625 "lexer_cocci.mll"
                   ( start_line true; mkassign Ast.DecRight lexbuf )
# 1411 "lexer_cocci.ml"

  | 48 ->
# 627 "lexer_cocci.mll"
                   ( start_line true; TDotDot (get_current_line_type lexbuf) )
# 1416 "lexer_cocci.ml"

  | 49 ->
# 629 "lexer_cocci.mll"
                   ( start_line true; TEqEq    (get_current_line_type lexbuf) )
# 1421 "lexer_cocci.ml"

  | 50 ->
# 630 "lexer_cocci.mll"
                   ( start_line true; TNotEq   (get_current_line_type lexbuf) )
# 1426 "lexer_cocci.ml"

  | 51 ->
# 631 "lexer_cocci.mll"
                   ( start_line true;
		     TLogOp(Ast.SupEq,get_current_line_type lexbuf) )
# 1432 "lexer_cocci.ml"

  | 52 ->
# 633 "lexer_cocci.mll"
                   ( start_line true;
		     if !Data.in_meta
		     then TSub(get_current_line_type lexbuf)
		     else TLogOp(Ast.InfEq,get_current_line_type lexbuf) )
# 1440 "lexer_cocci.ml"

  | 53 ->
# 637 "lexer_cocci.mll"
                   ( start_line true;
		     TLogOp(Ast.Inf,get_current_line_type lexbuf) )
# 1446 "lexer_cocci.ml"

  | 54 ->
# 639 "lexer_cocci.mll"
                   ( start_line true;
		     TLogOp(Ast.Sup,get_current_line_type lexbuf) )
# 1452 "lexer_cocci.ml"

  | 55 ->
# 642 "lexer_cocci.mll"
                   ( start_line true; TAndLog (get_current_line_type lexbuf) )
# 1457 "lexer_cocci.ml"

  | 56 ->
# 643 "lexer_cocci.mll"
                   ( start_line true; TOrLog  (get_current_line_type lexbuf) )
# 1462 "lexer_cocci.ml"

  | 57 ->
# 645 "lexer_cocci.mll"
                   ( start_line true;
		     TShROp(Ast.DecRight,get_current_line_type lexbuf) )
# 1468 "lexer_cocci.ml"

  | 58 ->
# 647 "lexer_cocci.mll"
                   ( start_line true;
		     TShLOp(Ast.DecLeft,get_current_line_type lexbuf) )
# 1474 "lexer_cocci.ml"

  | 59 ->
# 650 "lexer_cocci.mll"
                   ( start_line true; TAnd    (get_current_line_type lexbuf) )
# 1479 "lexer_cocci.ml"

  | 60 ->
# 651 "lexer_cocci.mll"
                   ( start_line true; TXor(get_current_line_type lexbuf) )
# 1484 "lexer_cocci.ml"

  | 61 ->
# 653 "lexer_cocci.mll"
                    ( start_line true; TCppConcatOp )
# 1489 "lexer_cocci.ml"

  | 62 ->
let
# 654 "lexer_cocci.mll"
                                                   def
# 1495 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_mem.(0)
and
# 655 "lexer_cocci.mll"
                                   ident
# 1500 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_mem.(0) lexbuf.Lexing.lex_curr_pos in
# 656 "lexer_cocci.mll"
      ( start_line true;
	let (arity,line,lline,offset,col,strbef,straft,pos) as lt =
	  get_current_line_type lexbuf in
	let off = String.length def in
	(* -1 in the code below because the ident is not at the line start *)
	TDefine
	  (lt,
	   check_var ident
	     (arity,line,lline,offset+off,col+off,[],[],Ast0.NoMetaPos)) )
# 1512 "lexer_cocci.ml"

  | 63 ->
let
# 665 "lexer_cocci.mll"
                                                   def
# 1518 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_mem.(0)
and
# 666 "lexer_cocci.mll"
                                    ident
# 1523 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_mem.(0) (lexbuf.Lexing.lex_curr_pos + -1) in
# 668 "lexer_cocci.mll"
      ( start_line true;
	let (arity,line,lline,offset,col,strbef,straft,pos) as lt =
	  get_current_line_type lexbuf in
	let off = String.length def in
	TDefineParam
        (lt,
	 check_var ident
	   (* why pos here but not above? *)
	   (arity,line,lline,offset+off,col+off,strbef,straft,pos),
	 offset + off + (String.length ident),
	 col + off + (String.length ident)) )
# 1537 "lexer_cocci.ml"

  | 64 ->
# 680 "lexer_cocci.mll"
      ( TIncludeL
	  (let str = tok lexbuf in
	  let start = String.index str '"' in
	  let finish = String.rindex str '"' in
	  start_line true;
	  (process_include start finish str,get_current_line_type lexbuf)) )
# 1547 "lexer_cocci.ml"

  | 65 ->
# 687 "lexer_cocci.mll"
      ( TIncludeNL
	  (let str = tok lexbuf in
	  let start = String.index str '<' in
	  let finish = String.rindex str '>' in
	  start_line true;
	  (process_include start finish str,get_current_line_type lexbuf)) )
# 1557 "lexer_cocci.ml"

  | 66 ->
# 700 "lexer_cocci.mll"
      ( start_line true; check_plus_linetype (tok lexbuf);
	TPragma (Ast.Noindent(tok lexbuf), get_current_line_type lexbuf) )
# 1563 "lexer_cocci.ml"

  | 67 ->
# 703 "lexer_cocci.mll"
      ( start_line true; check_plus_linetype (tok lexbuf);
	(* second argument to TPragma is not quite right, because
	   it represents only the first token of the comment, but that
	   should be good enough *)
	TPragma (Ast.Indent("/*"^(comment lexbuf)),
		 get_current_line_type lexbuf) )
# 1573 "lexer_cocci.ml"

  | 68 ->
# 710 "lexer_cocci.mll"
      ( (if !current_line_started
      then lexerr "--- must be at the beginning of the line" "");
	start_line true;
	TMinusFile
	  (let str = tok lexbuf in
	  (drop_spaces(String.sub str 3 (String.length str - 3)),
	   (get_current_line_type lexbuf))) )
# 1584 "lexer_cocci.ml"

  | 69 ->
# 718 "lexer_cocci.mll"
      ( (if !current_line_started
      then lexerr "+++ must be at the beginning of the line" "");
	start_line true;
	TPlusFile
	  (let str = tok lexbuf in
	  (drop_spaces(String.sub str 3 (String.length str - 3)),
	   (get_current_line_type lexbuf))) )
# 1595 "lexer_cocci.ml"

  | 70 ->
# 727 "lexer_cocci.mll"
      ( start_line true; id_tokens lexbuf )
# 1600 "lexer_cocci.ml"

  | 71 ->
# 729 "lexer_cocci.mll"
        ( start_line true;
	  TChar(char lexbuf,get_current_line_type lexbuf) )
# 1606 "lexer_cocci.ml"

  | 72 ->
# 731 "lexer_cocci.mll"
        ( start_line true;
	  TString(string lexbuf,(get_current_line_type lexbuf)) )
# 1612 "lexer_cocci.ml"

  | 73 ->
let
# 733 "lexer_cocci.mll"
             x
# 1618 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 733 "lexer_cocci.mll"
                   ( start_line true;
		     TFloat(x,(get_current_line_type lexbuf)) )
# 1623 "lexer_cocci.ml"

  | 74 ->
let
# 743 "lexer_cocci.mll"
         x
# 1629 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 743 "lexer_cocci.mll"
            ( start_line true; TInt(x,(get_current_line_type lexbuf)) )
# 1633 "lexer_cocci.ml"

  | 75 ->
# 745 "lexer_cocci.mll"
                   ( TIso )
# 1638 "lexer_cocci.ml"

  | 76 ->
# 746 "lexer_cocci.mll"
                   ( TRightIso )
# 1643 "lexer_cocci.ml"

  | 77 ->
# 748 "lexer_cocci.mll"
                   ( EOF )
# 1648 "lexer_cocci.ml"

  | 78 ->
# 750 "lexer_cocci.mll"
      ( lexerr "unrecognised symbol, in token rule: " (tok lexbuf) )
# 1653 "lexer_cocci.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and char lexbuf =
  __ocaml_lex_char_rec lexbuf 153
and __ocaml_lex_char_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 754 "lexer_cocci.mll"
          x
# 1665 "lexer_cocci.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 754 "lexer_cocci.mll"
                                                     ( String.make 1 x )
# 1669 "lexer_cocci.ml"

  | 1 ->
let
# 755 "lexer_cocci.mll"
                                             x
# 1675 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos (lexbuf.Lexing.lex_curr_pos + -1) in
# 755 "lexer_cocci.mll"
                                                     ( x )
# 1679 "lexer_cocci.ml"

  | 2 ->
let
# 756 "lexer_cocci.mll"
                                x
# 1685 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos (lexbuf.Lexing.lex_curr_pos + -1) in
# 756 "lexer_cocci.mll"
                                              ( x )
# 1689 "lexer_cocci.ml"

  | 3 ->
let
# 757 "lexer_cocci.mll"
                 v
# 1695 "lexer_cocci.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 1)
and
# 757 "lexer_cocci.mll"
                        x
# 1700 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos (lexbuf.Lexing.lex_start_pos + 2) in
# 758 "lexer_cocci.mll"
 ( (match v with
            | 'n' -> ()  | 't' -> ()   | 'v' -> ()  | 'b' -> ()
	    | 'r' -> ()  | 'f' -> () | 'a' -> ()
	    | '\\' -> () | '?'  -> () | '\'' -> ()  | '"' -> ()
            | 'e' -> ()
	    | _ -> lexerr "unrecognised symbol: " (tok lexbuf)
	    );
          x
	)
# 1712 "lexer_cocci.ml"

  | 4 ->
# 767 "lexer_cocci.mll"
      ( lexerr "unrecognised symbol: " (tok lexbuf) )
# 1717 "lexer_cocci.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_char_rec lexbuf __ocaml_lex_state

and string lexbuf =
  __ocaml_lex_string_rec lexbuf 168
and __ocaml_lex_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 770 "lexer_cocci.mll"
                                              ( "" )
# 1728 "lexer_cocci.ml"

  | 1 ->
let
# 771 "lexer_cocci.mll"
          x
# 1734 "lexer_cocci.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 771 "lexer_cocci.mll"
                               ( Common.string_of_char x ^ string lexbuf )
# 1738 "lexer_cocci.ml"

  | 2 ->
let
# 772 "lexer_cocci.mll"
                                            x
# 1744 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 772 "lexer_cocci.mll"
                                              ( x ^ string lexbuf )
# 1748 "lexer_cocci.ml"

  | 3 ->
let
# 773 "lexer_cocci.mll"
                               x
# 1754 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 773 "lexer_cocci.mll"
                                              ( x ^ string lexbuf )
# 1758 "lexer_cocci.ml"

  | 4 ->
let
# 774 "lexer_cocci.mll"
                v
# 1764 "lexer_cocci.ml"
= Lexing.sub_lexeme_char lexbuf (lexbuf.Lexing.lex_start_pos + 1)
and
# 774 "lexer_cocci.mll"
                       x
# 1769 "lexer_cocci.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos (lexbuf.Lexing.lex_start_pos + 2) in
# 775 "lexer_cocci.mll"
       (
         (match v with
	    | 'n' -> ()  | 't' -> ()   | 'v' -> ()  | 'b' -> () | 'r' -> ()
	    | 'f' -> () | 'a' -> ()
	    | '\\' -> () | '?'  -> () | '\'' -> ()  | '"' -> ()
	    | 'e' -> ()
	    | '\n' -> ()
	    | '(' -> () | '|' -> () | ')' -> ()
	    | _ -> lexerr "unrecognised symbol:" (tok lexbuf)
	 );
          x ^ string lexbuf
       )
# 1784 "lexer_cocci.ml"

  | 5 ->
# 787 "lexer_cocci.mll"
      ( lexerr "unrecognised symbol: " (tok lexbuf) )
# 1789 "lexer_cocci.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_string_rec lexbuf __ocaml_lex_state

and comment lexbuf =
  __ocaml_lex_comment_rec lexbuf 179
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 790 "lexer_cocci.mll"
         ( let s = tok lexbuf in check_comment s; start_line true; s )
# 1800 "lexer_cocci.ml"

  | 1 ->
# 792 "lexer_cocci.mll"
      ( let s = tok lexbuf in
        (* even blank line should have a + *)
        check_comment s;
        reset_line lexbuf; s ^ comment lexbuf )
# 1808 "lexer_cocci.ml"

  | 2 ->
# 796 "lexer_cocci.mll"
        ( pass_zero();
	  if !current_line_started
	  then (start_line true; let s = tok lexbuf in s^(comment lexbuf))
	  else (start_line true; comment lexbuf) )
# 1816 "lexer_cocci.ml"

  | 3 ->
# 802 "lexer_cocci.mll"
      ( let s = tok lexbuf in
        check_comment s; start_line true; s ^ comment lexbuf )
# 1822 "lexer_cocci.ml"

  | 4 ->
# 805 "lexer_cocci.mll"
      ( let s = tok lexbuf in
        check_comment s; start_line true; s ^ comment lexbuf )
# 1828 "lexer_cocci.ml"

  | 5 ->
# 808 "lexer_cocci.mll"
      ( start_line true; let s = tok lexbuf in
        Common.pr2 ("LEXER: unrecognised symbol in comment:"^s);
        s ^ comment lexbuf
      )
# 1836 "lexer_cocci.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

