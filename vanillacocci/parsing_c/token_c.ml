(* Yoann Padioleau
 *
 * Copyright (C) 2010, University of Copenhagen DIKU and INRIA.
 * Copyright (C) 2009 University of Urbana Champaign
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
(* Prelude *)
(*****************************************************************************)

(* This file may seems redundant with the tokens generated by Yacc
 * from parser.mly in parser_c.mli. The problem is that we need for
 * many reasons to remember in the ast_c the tokens invoved in this
 * ast, not just the string, especially for the comment and cpp_passed
 * tokens which pour le coup were not in the ast at all. So,
 * to avoid recursive mutual dependencies, we provide this file
 * so that ast_c does not need to depend on yacc which depends on
 * ast_c, etc.
 *
 * Also, ocamlyacc imposes some stupid constraints on the way we can define
 * the token type. ocamlyacc forces us to do a token type that
 * cant be a pair of a sum type, it must be directly a sum type.
 * We don't have this constraint here.
 *
 * Also, some yacc tokens are not used in the grammar because they are filtered
 * in some intermediate phases. But they still must be declared because
 * ocamllex may generate them, or some intermediate phase may also
 * generate them (like some functions in parsing_hacks.ml).
 * Here we don't have this problem again so we can have a clearer token type.
 *
 *
 *)

(*****************************************************************************)
(* Cpp constructs put in comments in lexer or parsing_hack *)
(*****************************************************************************)

(* history: was in ast_c.ml before:
 *  This type is not in the Ast but is associated with the TCommentCpp
 *  token. I put this enum here because parser_c.mly need it. I could have put
 *  it also in lexer_parser.
 *
 * update: now in token_c.ml, and actually right now we want those tokens
 * to be in the ast so that in the matching/transforming of C code, we
 * can detect if some metavariables match code which have some
 * cpp_passed tokens next to them (and so where we should issue a warning).
 *)
type cppcommentkind =
  | CppDirective
  | CppAttr
  | CppMacro
  | CppPassingNormal (* ifdef 0, cplusplus, etc *)
  | CppPassingCosWouldGetError (* expr passsing *)
  | CppPassingExplicit (* skip_start/end tag *)

(*****************************************************************************)
(* Types *)
(*****************************************************************************)

(*
 * TODO? Do we want to handle also non OriginTok-like tokens here ?
 * Right now we use this file to be able to later store in the
 * ast some information about comments and passed cpp tokens, to
 * improve our matching/transforming and unparsing in coccinelle.
 * So we should be concerned really only with origin tok, so right
 * now I use a simple Common.parse_info, not the more complex
 * Ast_c.parse_info, or even more complex Ast_c.info.
 * Also right now I defined only the token_tags of comment-like
 * tokens.
 *)

type info = Common.parse_info

(* I try to be consistent with the names in parser_c.mli *)
type token = token_tag * info
 and token_tag =
  | TCommentSpace
  | TCommentNewline

  | TComment

  (* the passed tokens because of our limited handling of cpp *)
  | TCommentCpp of cppcommentkind

  (*| TUnknown ? *)



(* Later if decide to include more kinds of tokens, then may
 * have to move the current token_tag like TCommentXxx in their
 * own type and have a generic TCommentLike of comment_like_token
 * in token_tag. Could also do like in token_helpers have some
 * is_xxx predicate, but it's not very pretty (but required when
 * some tokens can belong to multiple categories).
 *
 * It's supposed to be all the tokens that are not otherwise represented
 * in the ast via regular constructors and info.
 *)
type comment_like_token = token



(*****************************************************************************)
(* Getters *)
(*****************************************************************************)

(* simpler than in token_helpers :) because we don't have the ocamlyacc
 * constraints on how to define the token type. *)
let info_of_token = snd



(*****************************************************************************)
(*****************************************************************************)
(* remaining tokens

could define a type  token_class = Comment | Ident | Operator | ...

  | TInt of (string * Ast_c.info)
  | TFloat of ((string * Ast_c.floatType) * Ast_c.info)
  | TChar of ((string * Ast_c.isWchar) * Ast_c.info)
  | TString of ((string * Ast_c.isWchar) * Ast_c.info)

  | TIdent of (string * Ast_c.info)
  | TypedefIdent of (string * Ast_c.info)

  | TOPar of (Ast_c.info)
  | TCPar of (Ast_c.info)
  | TOBrace of (Ast_c.info)
  | TCBrace of (Ast_c.info)
  | TOCro of (Ast_c.info)
  | TCCro of (Ast_c.info)
  | TDot of (Ast_c.info)
  | TComma of (Ast_c.info)
  | TPtrOp of (Ast_c.info)
  | TInc of (Ast_c.info)
  | TDec of (Ast_c.info)
  | TAssign of (Ast_c.assignOp * Ast_c.info)
  | TEq of (Ast_c.info)
  | TWhy of (Ast_c.info)
  | TTilde of (Ast_c.info)
  | TBang of (Ast_c.info)
  | TEllipsis of (Ast_c.info)
  | TDotDot of (Ast_c.info)
  | TPtVirg of (Ast_c.info)
  | TOrLog of (Ast_c.info)
  | TAndLog of (Ast_c.info)
  | TOr of (Ast_c.info)
  | TXor of (Ast_c.info)
  | TAnd of (Ast_c.info)
  | TEqEq of (Ast_c.info)
  | TNotEq of (Ast_c.info)
  | TInf of (Ast_c.info)
  | TSup of (Ast_c.info)
  | TInfEq of (Ast_c.info)
  | TSupEq of (Ast_c.info)
  | TShl of (Ast_c.info)
  | TShr of (Ast_c.info)
  | TPlus of (Ast_c.info)
  | TMinus of (Ast_c.info)
  | TMul of (Ast_c.info)
  | TDiv of (Ast_c.info)
  | TMod of (Ast_c.info)
  | Tchar of (Ast_c.info)
  | Tshort of (Ast_c.info)
  | Tint of (Ast_c.info)
  | Tdouble of (Ast_c.info)
  | Tfloat of (Ast_c.info)
  | Tlong of (Ast_c.info)
  | Tunsigned of (Ast_c.info)
  | Tsigned of (Ast_c.info)
  | Tvoid of (Ast_c.info)
  | Tauto of (Ast_c.info)
  | Tregister of (Ast_c.info)
  | Textern of (Ast_c.info)
  | Tstatic of (Ast_c.info)
  | Ttypedef of (Ast_c.info)
  | Tconst of (Ast_c.info)
  | Tvolatile of (Ast_c.info)
  | Tstruct of (Ast_c.info)
  | Tunion of (Ast_c.info)
  | Tenum of (Ast_c.info)
  | Tbreak of (Ast_c.info)
  | Telse of (Ast_c.info)
  | Tswitch of (Ast_c.info)
  | Tcase of (Ast_c.info)
  | Tcontinue of (Ast_c.info)
  | Tfor of (Ast_c.info)
  | Tdo of (Ast_c.info)
  | Tif of (Ast_c.info)
  | Twhile of (Ast_c.info)
  | Treturn of (Ast_c.info)
  | Tgoto of (Ast_c.info)
  | Tdefault of (Ast_c.info)
  | Tsizeof of (Ast_c.info)
  | Trestrict of (Ast_c.info)
  | Tasm of (Ast_c.info)
  | Tattribute of (Ast_c.info)
  | Tinline of (Ast_c.info)
  | Ttypeof of (Ast_c.info)

  | TDefine of (Ast_c.info)
  | TDefParamVariadic of ((string * Ast_c.info))

  | TCppEscapedNewline of (Ast_c.info)

  | TOParDefine of (Ast_c.info)
  | TOBraceDefineInit of (Ast_c.info)
  | TIdentDefine of ((string * Ast_c.info))
  | TDefEOL of (Ast_c.info)
  | TInclude of ((string * string * bool ref * Ast_c.info))
  | TIncludeStart of ((Ast_c.info * bool ref))
  | TIncludeFilename of ((string * Ast_c.info))
  | TIfdef of (((int * int) option ref * Ast_c.info))
  | TIfdefelse of (((int * int) option ref * Ast_c.info))
  | TIfdefelif of (((int * int) option ref * Ast_c.info))
  | TEndif of (((int * int) option ref * Ast_c.info))
  | TIfdefBool of ((bool * (int * int) option ref * Ast_c.info))
  | TIfdefMisc of ((bool * (int * int) option ref * Ast_c.info))
  | TIfdefVersion of ((bool * (int * int) option ref * Ast_c.info))
  | TUndef of (string * Ast_c.info)
  | TCppDirectiveOther of (Ast_c.info)

  | TMacroAttr of ((string * Ast_c.info))
  | TMacroStmt of ((string * Ast_c.info))
  | TMacroString of ((string * Ast_c.info))
  | TMacroDecl of ((string * Ast_c.info))
  | TMacroDeclConst of (Ast_c.info)
  | TMacroStructDecl of ((string * Ast_c.info))
  | TMacroIterator of ((string * Ast_c.info))
  | TMacroAttrStorage of ((string * Ast_c.info))

  | TCommentSkipTagStart of (Ast_c.info)
  | TCommentSkipTagEnd of (Ast_c.info)

  | TCParEOL of (Ast_c.info)
  | TAction of (Ast_c.info)

  | TCommentMisc xxx

  | EOF of (Ast_c.info)
*)


(*****************************************************************************)
(* Helpers *)
(*****************************************************************************)
