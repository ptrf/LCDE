(* Yoann Padioleau
 *
 * Copyright (C) 2010, University of Copenhagen DIKU and INRIA.
 * Copyright (C) 2002, 2006, 2007, 2008, 2009 Yoann Padioleau
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License (GPL)
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * file license.txt for more details.
 *)
open Common

(*****************************************************************************)
(* The AST C related types *)
(*****************************************************************************)
(*
 * Some stuff are tagged semantic: which means that they are computed
 * after parsing.
 *
 * This means that some elements in this AST are present only if
 * some annotation/transformation has been done on the original AST returned
 * by the parser. Cf type_annotater, comment_annotater, cpp_ast_c, etc.
 *)


(* ------------------------------------------------------------------------- *)
(* Token/info *)
(* ------------------------------------------------------------------------- *)

(* To allow some transformations over the AST, we keep as much information
 * as possible in the AST such as the tokens content and their locations.
 * Those info are called 'info' (how original) and can be tagged.
 * For instance one tag may say that the unparser should remove this token.
 *
 * Update: Now I use a ref! in those 'info' so take care.
 * That means that modifications of the info of tokens can have
 * an effect on the info stored in the ast (which is sometimes
 * convenient, cf unparse_c.ml or comment_annotater_c.ml)
 *
 * convention: I often use 'ii' for the name of a list of info.
 *
 * Sometimes we want to add someting at the beginning or at the end
 * of a construct. For 'function' and 'decl' we want to add something
 * to their left and for 'if' 'while' et 'for' and so on at their right.
 * We want some kinds of "virtual placeholders" that represent the start or
 * end of a construct. We use fakeInfo for that purpose.
 * To identify those cases I have added a fakestart/fakeend comment.
 *
 * cocci: Each token will be decorated in the future by the mcodekind
 * of cocci. It is the job of the pretty printer to look at this
 * information and decide to print or not the token (and also the
 * pending '+' associated sometimes with the token).
 *
 * The first time that we parse the original C file, the mcodekind is
 * empty, or more precisely all is tagged as a CONTEXT with NOTHING
 * associated. This is what I call a "clean" expr/statement/....
 *
 * Each token will also be decorated in the future with an environment,
 * because the pending '+' may contain metavariables that refer to some
 * C code.
 *
 *)

(* forunparser: *)

type posl = int * int (* line-col, for MetaPosValList, for position variables *)
 (* with sexp *)

(* the virtual position is set in Parsing_hacks.insert_virtual_positions *)
type virtual_position = Common.parse_info * int (* character offset *)
 (* with sexp *)

type parse_info =
  (* Present both in ast and list of tokens *)
  | OriginTok of Common.parse_info
  (* Present only in ast and generated after parsing. Used mainly
   * by Julia, to add stuff at virtual places, beginning of func or decl *)
  | FakeTok of string * virtual_position
  (* Present both in ast and list of tokens.  *)
  | ExpandedTok of Common.parse_info * virtual_position

  (* Present neither in ast nor in list of tokens
   * but only in the '+' of the mcode of some tokens. Those kind of tokens
   * are used to be able to use '=' to compare big ast portions.
   *)
  | AbstractLineTok of Common.parse_info (* local to the abstracted thing *)
 (* with sexp *)

type info = {
  pinfo : parse_info;

  (* this cocci_tag can be changed, which is how we can express some program
   * transformations by tagging the tokens involved in this transformation.
   *)
  cocci_tag: (Ast_cocci.mcodekind * metavars_binding list) option ref;
  (* set in comment_annotater_c.ml *)
  comments_tag: comments_around ref;

  (* todo? token_info : sometimes useful to know what token it was *)
  }
and il = info list

(* wrap2 is like wrap, except that I use it often for separator such
 * as ','. In that case the info is associated to the argument that
 * follows, so in 'a,b' I will have in the list [(a,[]); (b,[','])].
 *
 * wrap3 is like wrap, except that I use it in case sometimes it
 * will be empty because the info will be included in a nested
 * entity (e.g. for Ident in expr because it's inlined in the name)
 * so user should never assume List.length wrap3 > 0.
 *)
and 'a wrap  = 'a * il
and 'a wrap2 = 'a * il
and 'a wrap3 = 'a * il (* * evotype*)

(* ------------------------------------------------------------------------- *)
(* Name *)
(* ------------------------------------------------------------------------- *)

(* was called 'ident' before, but 'name' is I think better
 * as concatenated strings can be used not only for identifiers and for
 * declarators, but also for fields, for labels, etc.
 *
 * Note: because now the info is embeded in the name, the info for
 * expression like Ident, or types like Typename, are not anymore
 * stored in the expression or type. Hence if you assume this,
 * which was true before, you are now wrong. So never write code like
 * let (unwrape,_), ii = e  and use 'ii' believing it contains
 * the local ii to e. If you want to do that, use the appropiate
 * wrapper get_local_ii_of_expr_inlining_ii_of_name.
 *)
and name =
   | RegularName of string wrap
   | CppConcatenatedName of (string wrap) wrap2 (* the ## separators *) list
   (* normally only used inside list of things, as in parameters or arguments
    * in which case, cf cpp-manual, it has a special meaning *)
   | CppVariadicName of string wrap (* ## s *)
   | CppIdentBuilder of string wrap (* s ( ) *) *
                       ((string wrap) wrap2 list) (* arguments *)


(* ------------------------------------------------------------------------- *)
(* C Type *)
(* ------------------------------------------------------------------------- *)
(* Could have more precise type in fullType, in expression, etc, but
 * it requires to do too much things in parsing such as checking no
 * conflicting structname, computing value, etc. Better to separate
 * concern. So I put '=>' to mean what we would really like. In fact
 * what we really like is defining another fullType, expression, etc
 * from scratch, because many stuff are just sugar.
 *
 * invariant: Array and FunctionType have also typeQualifier but they
 * dont have sense. I put this to factorise some code. If you look in
 * the grammar, you see that we can never specify const for the array
 * himself (but we can do it for pointer) or function, we always
 * have in the action rule of the grammar a { (nQ, FunctionType ...) }.
 *
 *
 * Because of ExprStatement, we can have more 'new scope' events, but
 * rare I think. For instance with 'array of constExpression' there can
 * have an exprStatement and a new (local) struct defined. Same for
 * Constructor.
 *
 *)


and fullType = typeQualifier * typeC
 and typeC = typeCbis wrap (* todo reput wrap3 *)

  and typeCbis =
  | BaseType        of baseType

  | Pointer         of fullType
  | Array           of constExpression option * fullType
  | FunctionType    of functionType

  | Enum            of string option * enumType
  | StructUnion     of structUnion * string option * structType (* new scope *)

  | EnumName        of string
  | StructUnionName of structUnion * string

  | TypeName   of name * fullType option (* semantic: filled later *)

  | ParenType of fullType (* forunparser: *)

  (* gccext: TypeOfType below may seems useless; Why declare a
   *     __typeof__(int) x; ?
   * When used with macros, it allows to fix a problem of C which
   * is that type declaration can be spread around the ident. Indeed it
   * may be difficult to have a macro such as
   *    '#define macro(type, ident) type ident;'
   * because when you want to do a
   *     macro(char[256], x),
   * then it will generate invalid code, but with a
   *       '#define macro(type, ident) __typeof(type) ident;'
   * it will work.
   *)
  | TypeOfExpr of expression
  | TypeOfType of fullType

  (* cppext: IfdefType TODO *)

(* -------------------------------------- *)
     and  baseType = Void
                   | IntType   of intType
		   | FloatType of floatType
		   | SizeType
		   | SSizeType
		   | PtrDiffType

	  (* stdC: type section
           * add  a | SizeT ?
           * note: char and signed char are semantically different!!
           *)
          and intType   = CChar (* obsolete? | CWchar  *)
	                | Si of signed

           and signed = sign * base
            and base = CChar2 | CShort | CInt | CLong | CLongLong (* gccext: *)
            and sign = Signed | UnSigned

          and floatType = CFloat | CDouble | CLongDouble


     (* -------------------------------------- *)
     and structUnion = Struct | Union
     and structType  = field list
         and field =
           | DeclarationField of field_declaration
           (* gccext: *)
           | EmptyField of info

            (* cppext: *)
           | MacroDeclField of (string * argument wrap2 list)
                               wrap (* optional ';'*)

            (* cppext: *)
           | CppDirectiveStruct of cpp_directive
           | IfdefStruct of ifdef_directive (* * field list list *)


        (* before unparser, I didn't have a FieldDeclList but just a Field. *)
         and field_declaration  =
           | FieldDeclList of fieldkind wrap2 list (* , *) wrap  (* ; *)

          (* At first I thought that a bitfield could be only Signed/Unsigned.
           * But it seems that gcc allow char i:4. C rule must say that you
           * can cast into int so enum too, ...
           *)
           and fieldkind =
             | Simple   of name option * fullType
             | BitField of name option * fullType *
                 info (* : *) * constExpression
              (* fullType => BitFieldInt | BitFieldUnsigned *)


     (* -------------------------------------- *)
     and enumType = oneEnumType wrap2 (* , *) list
                   (* => string * int list *)

     and oneEnumType = name * (info (* = *) * constExpression) option

     (* -------------------------------------- *)
     (* return * (params * has "...") *)
     and functionType = fullType * (parameterType wrap2 list * bool wrap)
        and parameterType =
        { p_namei: name option;
          p_register: bool wrap;
          p_type: fullType;
        }
        (* => (bool (register) * fullType) list * bool *)


and typeQualifier = typeQualifierbis wrap
and typeQualifierbis = {const: bool; volatile: bool}

(* gccext: cppext: *)
and attribute = attributebis wrap
  and attributebis =
    | Attribute of string

(* ------------------------------------------------------------------------- *)
(* C expression *)
(* ------------------------------------------------------------------------- *)
and expression = (expressionbis * exp_info ref (* semantic: *)) wrap3
 and exp_info = exp_type option * test
  and exp_type = fullType (* Type_c.completed_and_simplified *) * local
    and local = LocalVar of parse_info | NotLocalVar (* cocci: *)
  and test = Test | NotTest (* cocci: *)

 and expressionbis =

  (* Ident can be a enumeration constant, a simple variable, a name of a func.
   * With cppext, Ident can also be the name of a macro. Sparse says
   * "an identifier with a meaning is a symbol" *)
  | Ident          of name (* todo? more semantic info such as LocalFunc *)

  | Constant       of constant
  | FunCall        of expression * argument wrap2 (* , *) list
  (* gccext: x ? /* empty */ : y <=> x ? x : y;  hence the 'option' below *)
  | CondExpr       of expression * expression option * expression

  (* should be considered as statements, bad C langage *)
  | Sequence       of expression * expression
  | Assignment     of expression * assignOp * expression


  | Postfix        of expression * fixOp
  | Infix          of expression * fixOp

  | Unary          of expression * unaryOp
  | Binary         of expression * binaryOp * expression

  | ArrayAccess    of expression * expression

  (* field ident access *)
  | RecordAccess   of expression * name
  | RecordPtAccess of expression * name
  (* redundant normally, could replace it by DeRef RecordAcces *)

  | SizeOfExpr     of expression
  | SizeOfType     of fullType
  | Cast           of fullType * expression

  (* gccext: *)
  | StatementExpr of compound wrap (* ( )     new scope *)
  | Constructor  of fullType * initialiser wrap2 (* , *) list

  (* forunparser: *)
  | ParenExpr of expression

  (* cppext: IfdefExpr TODO *)

  (* cppext: normmally just expression *)
  and argument = (expression, weird_argument) Common.either
   and weird_argument =
       | ArgType of parameterType
       | ArgAction of action_macro
      and action_macro =
        (* todo: ArgStatement of statement, possibly have ghost token *)
         | ActMisc of il


  (* I put string for Int and Float because int would not be enough because
   * OCaml int are 31 bits. So simpler to do string. Same reason to have
   * string instead of int list for the String case.
   *
   * note: -2 is not a constant, it is the unary operator '-'
   * applied to constant 2. So the string must represent a positive
   * integer only. *)

  and constant =
    | String of (string * isWchar)
    | MultiString of string list (* can contain MacroString, todo: more info *)
    | Char   of (string * isWchar) (* normally it is equivalent to Int *)
    | Int    of (string * intType)
    | Float  of (string * floatType)

    and isWchar = IsWchar | IsChar


  and unaryOp  = GetRef | DeRef | UnPlus |  UnMinus | Tilde | Not
                 | GetRefLabel (* gccext: GetRefLabel, via &&label notation *)
  and assignOp = SimpleAssign | OpAssign of arithOp
  and fixOp    = Dec | Inc

  and binaryOp = Arith of arithOp | Logical of logicalOp

       and arithOp   =
         | Plus | Minus | Mul | Div | Mod
         | DecLeft | DecRight
         | And | Or | Xor

       and logicalOp =
         | Inf | Sup | InfEq | SupEq
         | Eq | NotEq
         | AndLog | OrLog

 and constExpression = expression (* => int *)


(* ------------------------------------------------------------------------- *)
(* C statement *)
(* ------------------------------------------------------------------------- *)
(* note: that assignement is not a statement but an expression;
 * wonderful C langage.
 *
 * note: I use 'and' for type definition cos gccext allow statement as
 * expression, so need mutual recursive type definition.
 *
 *)

and statement = statementbis wrap3
 and statementbis =
  | Labeled       of labeled
  | Compound      of compound   (* new scope *)
  | ExprStatement of exprStatement
  | Selection     of selection (* have fakeend *)
  | Iteration     of iteration (* have fakeend *)
  | Jump          of jump

  (* simplify cocci: only at the beginning of a compound normally *)
  | Decl  of declaration

  (* gccext: *)
  | Asm of asmbody
  | NestedFunc of definition

  (* cppext: *)
  | MacroStmt



  and labeled = Label   of name * statement
              | Case    of expression * statement
              | CaseRange of expression * expression * statement (* gccext: *)
	      |	Default of statement

  (* cppext:
   * old: compound = (declaration list * statement list)
   * old: (declaration, statement) either list
   * Simplify cocci to just have statement list, by integrating Decl in stmt.
   *
   * update: now introduce also the _sequencable to allow ifdef in the middle.
   * Indeed, I now allow ifdefs in the ast but they must be only between
   * "sequencable" elements. They can be put in a type only if this type
   * is used in a list, like at the toplevel, used in a 'toplevel list',
   * or inside a compound, used in a 'statement list'. I must not allow
   * ifdef anywhere. For instance I can not make ifdef a statement
   * cos some instruction like If accept only one statement and the
   * ifdef directive must not take the place of a legitimate instruction.
   * We had a similar phenomena in SmPL where we have the notion
   * of statement and sequencable statement too. Once you have
   * such a type of sequencable thing, then s/xx list/xx_sequencable list/
   * and introduce the ifdef.
   *
   * update: those ifdefs are either passed, or present in the AST but in
   * a flat form. To structure those flat ifdefs you have to run
   * a transformation that will put in a tree the statements inside
   * ifdefs branches. Cf cpp_ast_c.ml. This is for instance the difference
   * between a IfdefStmt (flat) and IfdefStmt2 (tree structured).
   *
   *)
  and compound = statement_sequencable list

  (* cppext: easier to put at statement_list level than statement level *)
  and statement_sequencable =
    | StmtElem of statement

    (* cppext: *)
    | CppDirectiveStmt of cpp_directive
    | IfdefStmt of ifdef_directive

    (* this will be build in cpp_ast_c from the previous flat IfdefStmt *)
    | IfdefStmt2 of ifdef_directive list * (statement_sequencable list) list

  and exprStatement = expression option

 (* for Switch, need check that all elements in the compound start
  * with a case:, otherwise unreachable code.
  *)
  and selection     =
   | If     of expression * statement * statement
   | Switch of expression * statement


  and iteration     =
    | While   of expression * statement
    | DoWhile of statement * expression
    | For     of exprStatement wrap * exprStatement wrap * exprStatement wrap *
                 statement
    (* cppext: *)
    | MacroIteration of string * argument wrap2 list * statement

  and jump  = Goto of name
            | Continue | Break
            | Return   | ReturnExpr of expression
            | GotoComputed of expression (* gccext: goto *exp ';' *)


  (* gccext: *)
  and asmbody = il (* string list *) * colon wrap (* : *) list
      and colon = Colon of colon_option wrap2 list
      and colon_option = colon_option_bis wrap
          and colon_option_bis = ColonMisc | ColonExpr of expression


(* ------------------------------------------------------------------------- *)
(* Declaration *)
(* ------------------------------------------------------------------------- *)
(* (string * ...) option cos can have empty declaration or struct tag
 * declaration.
 *
 * Before I had a Typedef constructor, but why make this special case and not
 * have StructDef, EnumDef, ... so that 'struct t {...} v' will generate 2
 * declarations ? So I try to generalise and not have Typedef either. This
 * requires more work in parsing. Better to separate concern.
 *
 * Before the need for unparser, I didn't have a DeclList but just a Decl.
 *
 * I am not sure what it means to declare a prototype inline, but gcc
 * accepts it.
 *)

and declaration =
  | DeclList of onedecl wrap2 (* , *) list wrap (* ; fakestart sto *)
  (* cppext: *)
  | MacroDecl of (string * argument wrap2 list) wrap (* fakestart *)

     and onedecl =
       { v_namei: (name * (info (* = *) * initialiser) option) option;
         v_type: fullType;
         (* semantic: set in type annotated and used in cocci_vs_c
          * when we transform some initialisation into affectation
          *)
         v_type_bis: fullType (* Type_c.completed_and_simplified *) option ref;
         v_storage: storage;
         v_local: local_decl; (* cocci: *)
         v_attr: attribute list; (* gccext: *)
       }
     and storage       = storagebis * bool (* gccext: inline or not *)
     and storagebis    = NoSto | StoTypedef | Sto of storageClass
     and storageClass  = Auto  | Static | Register | Extern

     and local_decl = LocalDecl | NotLocalDecl

     (* fullType is the type used if the type should be converted to
	an assignment.  It can be adjusted in the type annotation
	phase when typedef information is availalble *)
     and initialiser = initialiserbis wrap
       and initialiserbis =
          | InitExpr of expression
          | InitList of initialiser wrap2 (* , *) list
          (* gccext: *)
          | InitDesignators of designator list * initialiser
          | InitFieldOld  of string * initialiser
          | InitIndexOld  of expression * initialiser

       (* ex: [2].y = x,  or .y[2]  or .y.x. They can be nested *)
       and designator = designatorbis wrap
        and designatorbis =
            | DesignatorField of string
            | DesignatorIndex of expression
            | DesignatorRange of expression * expression

(* ------------------------------------------------------------------------- *)
(* Function definition *)
(* ------------------------------------------------------------------------- *)
(* Normally we should define another type functionType2 because there
 * are more restrictions on what can define a function than a pointer
 * function. For instance a function declaration can omit the name of the
 * parameter whereas a function definition can not. But, in some cases such
 * as 'f(void) {', there is no name too, so I simplified and reused the
 * same functionType type for both declaration and function definition.
 *
 * Also old style C does not have type in the parameter, so again simpler
 * to abuse the functionType and allow missing type.
 *)
and definition = definitionbis wrap (* ( ) { } fakestart sto *)
  and definitionbis =
  { f_name: name;
    f_type: functionType; (* less? a functionType2 ? *)
    f_storage: storage;
    f_body: compound;
    f_attr: attribute list; (* gccext: *)
    f_old_c_style: declaration list option;
  }
  (* cppext: IfdefFunHeader TODO *)

(* ------------------------------------------------------------------------- *)
(* cppext: cpp directives, #ifdef, #define and #include body *)
(* ------------------------------------------------------------------------- *)
and cpp_directive =
  | Define of define
  | Include of includ
  | Undef of string wrap
  | PragmaAndCo of il
(*| Ifdef ? no, ifdefs are handled differently, cf ifdef_directive below *)

and define = string wrap (* #define s eol *) * (define_kind * define_val)
   and define_kind =
   | DefineVar
   | DefineFunc   of ((string wrap) wrap2 list) wrap (* () *)
   and define_val =
     (* most common case; e.g. to define int constant *)
     | DefineExpr of expression

     | DefineStmt of statement
     | DefineType of fullType
     | DefineDoWhileZero of (statement * expression) wrap (* do { } while(0) *)

     | DefineFunction of definition
     | DefineInit of initialiser (* in practice only { } with possible ',' *)

     (* TODO DefineMulti of define_val list *)

     | DefineText of string wrap
     | DefineEmpty

     | DefineTodo



and includ =
  { i_include: inc_file wrap; (* #include s *)
    (* cocci: computed in ? *)
    i_rel_pos: include_rel_pos option ref;
    (* cocci: cf -test incl *)
    i_is_in_ifdef: bool;
    (* cf cpp_ast_c.ml. set to None at parsing time. *)
    i_content: (Common.filename (* full path *) * program) option;
  }
 and inc_file =
  | Local    of inc_elem list
  | NonLocal of inc_elem list
  | Weird of string (* ex: #include SYSTEM_H *)
  and inc_elem = string

 (* cocci: to tag the first of #include <xx/> and last of #include <yy/>
  *
  * The first_of and last_of store the list of prefixes that was
  * introduced by the include. On #include <a/b/x>, if the include was
  * the first in the file, it would give in first_of the following
  * prefixes a/b/c; a/b/; a/ ; <empty>
  *
  * This is set after parsing, in cocci.ml, in update_rel_pos.
  *)
 and include_rel_pos = {
   first_of : string list list;
   last_of :  string list list;
 }



(* todo? to specialize if someone need more info *)
and ifdef_directive = (* or and 'a ifdefed = 'a list wrap *)
  | IfdefDirective of (ifdefkind * matching_tag) wrap
  and ifdefkind =
    | Ifdef (* todo? of string ? of formula_cpp ? *)
    | IfdefElseif (* same *)
    | IfdefElse (* same *)
    | IfdefEndif
  (* set in Parsing_hacks.set_ifdef_parenthize_info. It internally use
   * a global so it means if you parse the same file twice you may get
   * different id. I try now to avoid this pb by resetting it each
   * time I parse a file.
   *)
  and matching_tag =
    IfdefTag of (int (* tag *) * int (* total with this tag *))





(* ------------------------------------------------------------------------- *)
(* The toplevels elements *)
(* ------------------------------------------------------------------------- *)
and toplevel =
  | Declaration of declaration
  | Definition of definition

  (* cppext: *)
  | CppTop of cpp_directive
  | IfdefTop of ifdef_directive (* * toplevel list *)

  (* cppext: *)
  | MacroTop of string * argument wrap2 list * il

  | EmptyDef of il      (* gccext: allow redundant ';' *)
  | NotParsedCorrectly of il

  | FinalDef of info (* EOF *)

(* ------------------------------------------------------------------------- *)
and program = toplevel list

(*****************************************************************************)
(* Cocci Bindings *)
(*****************************************************************************)
(* Was previously in pattern.ml, but because of the transformer,
 * we need to decorate each token with some cocci code AND the environment
 * for this cocci code.
 *)
and metavars_binding = (Ast_cocci.meta_name, metavar_binding_kind) assoc
  and metavar_binding_kind =
  | MetaIdVal        of string *
	                Ast_cocci.meta_name list (* negative constraints *)
  | MetaFuncVal      of string
  | MetaLocalFuncVal of string

  | MetaExprVal      of expression (* a "clean expr" *) *
	                (*subterm constraints, currently exprs*)
	                Ast_cocci.meta_name list
  | MetaExprListVal  of argument wrap2 list
  | MetaParamVal     of parameterType
  | MetaParamListVal of parameterType wrap2 list

  | MetaTypeVal      of fullType
  | MetaInitVal      of initialiser
  | MetaDeclVal      of declaration
  | MetaFieldVal     of field
  | MetaStmtVal      of statement

  (* Could also be in Lib_engine.metavars_binding2 with the ParenVal,
   * because don't need to have the value for a position in the env of
   * a '+'. But ParenVal or LabelVal are used only by CTL, they are not
   * variables accessible via SmPL whereas the position can be one day
   * so I think it's better to put MetaPosVal here *)
  | MetaPosVal       of (Ast_cocci.fixpos * Ast_cocci.fixpos) (* max, min *)
  | MetaPosValList   of
      (Common.filename * string (*element*) * posl * posl) list (* min, max *)
  | MetaListlenVal   of int


(*****************************************************************************)
(* C comments *)
(*****************************************************************************)

(* convention: I often use "m" for comments as I can not use "c"
 * (already use for c stuff) and "com" is too long.
 *)

(* this type will be associated to each token.
 *)
and comments_around = {
  mbefore: Token_c.comment_like_token list;
  mafter:  Token_c.comment_like_token list;

  (* less: could remove ? do something simpler than CComment for
   * coccinelle, cf above. *)
  mbefore2: comment_and_relative_pos list;
  mafter2:  comment_and_relative_pos list;
  }
  and comment_and_relative_pos = {

   minfo: Common.parse_info;
   (* the int represent the number of lines of difference between the
    * current token and the comment. When on same line, this number is 0.
    * When previous line, -1. In some way the after/before in previous
    * record is useless because the sign of the integer can helps
    * do the difference too, but I keep it that way.
    *)
   mpos: int;
   (* todo?
    *  cppbetween: bool; touse? if false positive
    *  is_alone_in_line: bool; (*for labels, to avoid false positive*)
   *)
  }

and comment = Common.parse_info
and com = comment list ref

 (* with sexp *)


(*****************************************************************************)
(* Some constructors *)
(*****************************************************************************)
let nullQualif = ({const=false; volatile= false}, [])
let nQ = nullQualif

let defaultInt = (BaseType (IntType (Si (Signed, CInt))))

let noType () = ref (None,NotTest)
let noInstr = (ExprStatement (None), [])
let noTypedefDef () = None

let emptyMetavarsBinding =
  ([]: metavars_binding)

let emptyAnnotCocci =
  (Ast_cocci.CONTEXT (Ast_cocci.NoPos,Ast_cocci.NOTHING),
  ([] : metavars_binding list))

let emptyAnnot =
  (None: (Ast_cocci.mcodekind * metavars_binding list) option)

(* compatibility mode *)
let mcode_and_env_of_cocciref aref =
  match !aref with
  | Some x -> x
  | None -> emptyAnnotCocci


let emptyComments= {
  mbefore = [];
  mafter = [];
  mbefore2 = [];
  mafter2 = [];
}


(* for include, some meta information needed by cocci *)
let noRelPos () =
  ref (None: include_rel_pos option)
let noInIfdef () =
  ref false


(* When want add some info in ast that does not correspond to
 * an existing C element.
 * old: or when don't want 'synchronize' on it in unparse_c.ml
 * (now have other mark for tha matter).
 *)
let no_virt_pos = ({str="";charpos=0;line=0;column=0;file=""},-1)

let fakeInfo pi  =
  { pinfo = FakeTok ("",no_virt_pos);
    cocci_tag = ref emptyAnnot;
    comments_tag = ref emptyComments;
  }

let noii = []
let noattr = []
let noi_content = (None: ((Common.filename * program) option))

(*****************************************************************************)
(* Wrappers *)
(*****************************************************************************)
let unwrap = fst

let unwrap2 = fst

let unwrap_expr ((unwrap_e, typ), iie) = unwrap_e
let rewrap_expr ((_old_unwrap_e, typ), iie)  newe = ((newe, typ), iie)

let unwrap_typeC (qu, (typeC, ii)) = typeC
let rewrap_typeC (qu, (typeC, ii)) newtypeC  = (qu, (newtypeC, ii))

let unwrap_typeCbis (typeC, ii) = typeC

let unwrap_st (unwrap_st, ii) = unwrap_st

(* ------------------------------------------------------------------------- *)
let mk_e unwrap_e ii = (unwrap_e, noType()), ii
let mk_e_bis unwrap_e ty ii = (unwrap_e, ty), ii

let mk_ty typeC ii = nQ, (typeC, ii)
let mk_tybis typeC ii = (typeC, ii)

let mk_st unwrap_st ii = (unwrap_st, ii)

(* ------------------------------------------------------------------------- *)
let get_ii_typeC_take_care (typeC, ii) = ii
let get_ii_st_take_care (st, ii) = ii
let get_ii_expr_take_care (e, ii) = ii

let get_st_and_ii (st, ii) = st, ii
let get_ty_and_ii (qu, (typeC, ii)) = qu, (typeC, ii)
let get_e_and_ii  (e, ii) = e, ii


(* ------------------------------------------------------------------------- *)
let get_type_expr ((unwrap_e, typ), iie) = !typ
let set_type_expr ((unwrap_e, oldtyp), iie) newtyp =
  oldtyp := newtyp
  (* old: (unwrap_e, newtyp), iie *)

let get_onlytype_expr ((unwrap_e, typ), iie) =
  match !typ with
  | Some (ft,_local), _test -> Some ft
  | None, _ -> None

let get_onlylocal_expr ((unwrap_e, typ), iie) =
  match !typ with
  | Some (ft,local), _test -> Some local
  | None, _ -> None

(* ------------------------------------------------------------------------- *)
let rewrap_str s ii =
  {ii with pinfo =
    (match ii.pinfo with
      OriginTok pi -> OriginTok { pi with Common.str = s;}
    | ExpandedTok (pi,vpi) -> ExpandedTok ({ pi with Common.str = s;},vpi)
    | FakeTok (_,vpi) -> FakeTok (s,vpi)
    | AbstractLineTok pi -> OriginTok { pi with Common.str = s;})}

let rewrap_pinfo pi ii =
  {ii with pinfo = pi}



(* info about the current location *)
let get_pi = function
    OriginTok pi -> pi
  | ExpandedTok (_,(pi,_)) -> pi
  | FakeTok (_,(pi,_)) -> pi
  | AbstractLineTok pi -> pi

(* original info *)
let get_opi = function
    OriginTok pi -> pi
  | ExpandedTok (pi,_) -> pi (* diff with get_pi *)
  | FakeTok (_,_) -> failwith "no position information"
  | AbstractLineTok pi -> pi

let str_of_info ii =
  match ii.pinfo with
    OriginTok pi -> pi.Common.str
  | ExpandedTok (pi,_) -> pi.Common.str
  | FakeTok (s,_) -> s
  | AbstractLineTok pi -> pi.Common.str

let get_info f ii =
  match ii.pinfo with
    OriginTok pi -> f pi
  | ExpandedTok (_,(pi,_)) -> f pi
  | FakeTok (_,(pi,_)) -> f pi
  | AbstractLineTok pi -> f pi

let get_orig_info f ii =
  match ii.pinfo with
    OriginTok pi -> f pi
  | ExpandedTok (pi,_) -> f pi (* diff with get_info *)
  | FakeTok (_,(pi,_)) -> f pi
  | AbstractLineTok pi -> f pi

let make_expanded ii =
  {ii with pinfo = ExpandedTok (get_opi ii.pinfo,no_virt_pos)}

let pos_of_info   ii = get_info      (function x -> x.Common.charpos) ii
let opos_of_info  ii = get_orig_info (function x -> x.Common.charpos) ii
let line_of_info  ii = get_orig_info (function x -> x.Common.line)    ii
let col_of_info   ii = get_orig_info (function x -> x.Common.column)  ii
let file_of_info  ii = get_orig_info (function x -> x.Common.file)    ii
let mcode_of_info ii = fst (mcode_and_env_of_cocciref ii.cocci_tag)
let pinfo_of_info ii = ii.pinfo
let parse_info_of_info ii = get_pi ii.pinfo

let strloc_of_info ii =
  spf "%s:%d" (file_of_info ii) (line_of_info ii)

let is_fake ii =
  match ii.pinfo with
    FakeTok (_,_) -> true
  | _ -> false

let is_origintok ii =
  match ii.pinfo with
  | OriginTok pi -> true
  | _ -> false

(* ------------------------------------------------------------------------- *)
type posrv = Real of Common.parse_info | Virt of virtual_position

let compare_pos ii1 ii2 =
  let get_pos = function
      OriginTok pi -> Real pi
    | FakeTok (s,vpi) -> Virt vpi
    | ExpandedTok (pi,vpi) -> Virt vpi
    | AbstractLineTok pi -> Real pi in (* used for printing *)
  let pos1 = get_pos (pinfo_of_info ii1) in
  let pos2 = get_pos (pinfo_of_info ii2) in
  match (pos1,pos2) with
    (Real p1, Real p2) ->
      compare p1.Common.charpos p2.Common.charpos
  | (Virt (p1,_), Real p2) ->
      if (compare p1.Common.charpos p2.Common.charpos) =|= (-1) then (-1) else 1
  | (Real p1, Virt (p2,_)) ->
      if (compare p1.Common.charpos p2.Common.charpos) =|= 1 then 1 else (-1)
  | (Virt (p1,o1), Virt (p2,o2)) ->
      let poi1 = p1.Common.charpos in
      let poi2 = p2.Common.charpos in
      match compare poi1 poi2 with
	-1 -> -1
      |	0 -> compare o1 o2
      |	x -> x

let equal_posl (l1,c1) (l2,c2) =
  (l1 =|= l2) && (c1 =|= c2)

let info_to_fixpos ii =
  match pinfo_of_info ii with
    OriginTok pi -> Ast_cocci.Real pi.Common.charpos
  | ExpandedTok (_,(pi,offset)) ->
      Ast_cocci.Virt (pi.Common.charpos,offset)
  | FakeTok (_,(pi,offset)) ->
      Ast_cocci.Virt (pi.Common.charpos,offset)
  | AbstractLineTok pi -> failwith "unexpected abstract"

(* cocci: *)
let is_test (e : expression) =
  let (_,info), _ = e in
  let (_,test) = !info in
  test =*= Test

(*****************************************************************************)
(* Abstract line *)
(*****************************************************************************)

(* When we have extended the C Ast to add some info to the tokens,
 * such as its line number in the file, we can not use anymore the
 * ocaml '=' to compare Ast elements. To overcome this problem, to be
 * able to use again '=', we just have to get rid of all those extra
 * information, to "abstract those line" (al) information.
 *
 * Julia then modifies it a little to have a tokenindex, so the original
 * true al_info is in fact real_al_info.
 *)

let al_info tokenindex x =
  { pinfo =
    (AbstractLineTok
       {charpos = tokenindex;
	 line = tokenindex;
	 column = tokenindex;
	 file = "";
	 str = str_of_info x});
    cocci_tag = ref emptyAnnot;
    comments_tag = ref emptyComments;
  }

let semi_al_info x =
  { x with
    cocci_tag = ref emptyAnnot;
    comments_tag = ref emptyComments;
  }

let magic_real_number = -10

let real_al_info x =
  { pinfo =
    (AbstractLineTok
       {charpos = magic_real_number;
	 line = magic_real_number;
	 column = magic_real_number;
	 file = "";
	 str = str_of_info x});
    cocci_tag = ref emptyAnnot;
    comments_tag = ref emptyComments;
  }

let al_comments x =
  let keep_cpp l =
    List.filter (function (Token_c.TCommentCpp _,_) -> true | _ -> false) l in
  let al_com (x,i) =
    (x,{i with Common.charpos = magic_real_number;
	 Common.line = magic_real_number;
	 Common.column = magic_real_number}) in
  {mbefore = []; (* duplicates mafter of the previous token *)
   mafter = List.map al_com (keep_cpp x.mafter);
   mbefore2=[];
   mafter2=[];
  }

let al_info_cpp tokenindex x =
  { pinfo =
    (AbstractLineTok
       {charpos = tokenindex;
	 line = tokenindex;
	 column = tokenindex;
	 file = "";
	 str = str_of_info x});
    cocci_tag = ref emptyAnnot;
    comments_tag = ref (al_comments !(x.comments_tag));
  }

let semi_al_info_cpp x =
  { x with
    cocci_tag = ref emptyAnnot;
    comments_tag = ref (al_comments !(x.comments_tag));
  }

let real_al_info_cpp x =
  { pinfo =
    (AbstractLineTok
       {charpos = magic_real_number;
	 line = magic_real_number;
	 column = magic_real_number;
	 file = "";
	 str = str_of_info x});
    cocci_tag = ref emptyAnnot;
    comments_tag =  ref (al_comments !(x.comments_tag));
  }


(*****************************************************************************)
(* Views *)
(*****************************************************************************)

(* Transform a list of arguments (or parameters) where the commas are
 * represented via the wrap2 and associated with an element, with
 * a list where the comma are on their own. f(1,2,2) was
 * [(1,[]); (2,[,]); (2,[,])] and become [1;',';2;',';2].
 *
 * Used in cocci_vs_c.ml, to have a more direct correspondance between
 * the ast_cocci of julia and ast_c.
 *)
let rec (split_comma: 'a wrap2 list -> ('a, il) either list) =
  function
  | [] -> []
  | (e, ii)::xs ->
      if null ii
      then (Left e)::split_comma xs
      else Right ii::Left e::split_comma xs

let rec (unsplit_comma: ('a, il) either list -> 'a wrap2 list) =
  function
  | [] -> []
  | Right ii::Left e::xs ->
      (e, ii)::unsplit_comma xs
  | Left e::xs ->
      let empty_ii = [] in
      (e, empty_ii)::unsplit_comma xs
  | Right ii::_ ->
      raise Impossible




(*****************************************************************************)
(* Helpers, could also be put in lib_parsing_c.ml instead *)
(*****************************************************************************)

(* should maybe be in pretty_print_c ? *)

let s_of_inc_file inc_file =
  match inc_file with
  | Local xs -> xs +> Common.join "/"
  | NonLocal xs -> xs +> Common.join "/"
  | Weird s -> s

let s_of_inc_file_bis inc_file =
  match inc_file with
  | Local xs -> "\"" ^ xs +> Common.join "/" ^ "\""
  | NonLocal xs -> "<" ^ xs +> Common.join "/" ^ ">"
  | Weird s -> s

let fieldname_of_fieldkind fieldkind =
  match fieldkind with
  | Simple (sopt, ft) -> sopt
  | BitField (sopt, ft, info, expr) -> sopt


let s_of_attr attr =
  attr
  +> List.map (fun (Attribute s, ii) -> s)
  +> Common.join ","


(* ------------------------------------------------------------------------- *)
let str_of_name ident =
  match ident with
  | RegularName (s,ii) -> s
  | CppConcatenatedName xs ->
      xs +> List.map (fun (x,iiop) -> unwrap x) +> Common.join "##"
  | CppVariadicName (s, ii) -> "##" ^ s
  | CppIdentBuilder ((s,iis), xs) ->
      s ^ "(" ^
        (xs +> List.map (fun ((x,iix), iicomma) -> x) +> Common.join ",") ^
        ")"

let get_s_and_ii_of_name name =
  match name with
  | RegularName (s, iis) -> s, iis
  | CppIdentBuilder ((s, iis), xs) -> s, iis
  | CppVariadicName (s,iis)  ->
      let (iop, iis) = Common.tuple_of_list2 iis in
      s, [iis]
  | CppConcatenatedName xs ->
      (match xs with
      | [] -> raise Impossible
      | ((s,iis),noiiop)::xs ->
          s, iis
      )

let get_s_and_info_of_name name =
  let (s,ii) = get_s_and_ii_of_name name in
  s, List.hd ii

let info_of_name name =
  let (s,ii) = get_s_and_ii_of_name name in
  List.hd ii

let ii_of_name name =
  let (s,ii) = get_s_and_ii_of_name name in
  ii

let get_local_ii_of_expr_inlining_ii_of_name e =
  let (ebis,_),ii = e in
  match ebis, ii with
  | Ident name, noii ->
      assert(null noii);
      ii_of_name name
  | RecordAccess   (e, name), ii ->
      ii @ ii_of_name name
  | RecordPtAccess (e, name), ii ->
      ii @ ii_of_name name
  | _, ii -> ii


let get_local_ii_of_tybis_inlining_ii_of_name ty =
  match ty with
  | TypeName (name, _typ), [] -> ii_of_name name
  | _, ii -> ii

(* the following is used to obtain the argument to LocalVar *)
let info_of_type ft =
  let (qu, ty) = ft in
  (* bugfix: because of string->name, the ii can be deeper *)
  let ii = get_local_ii_of_tybis_inlining_ii_of_name ty in
  match ii with
  | ii::_ -> ii.pinfo
  | [] -> failwith "type has no text; need to think again"

(* only Label and Goto have name *)
let get_local_ii_of_st_inlining_ii_of_name st =
  match st with
  | Labeled (Label (name, st)), ii -> ii_of_name name @ ii
  | Jump (Goto name), ii ->
      let (i1, i3) = Common.tuple_of_list2 ii in
      [i1] @ ii_of_name name @ [i3]
  | _, ii -> ii



(* ------------------------------------------------------------------------- *)
let name_of_parameter param =
  param.p_namei +> Common.map_option (str_of_name)

