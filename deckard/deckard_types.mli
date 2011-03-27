module A :
  sig
    type posl = int * int
    type virtual_position = Common.parse_info * int
    type parse_info =
      Ast_c.parse_info =
        OriginTok of Common.parse_info
      | FakeTok of string * virtual_position
      | ExpandedTok of Common.parse_info * virtual_position
      | AbstractLineTok of Common.parse_info
    type info =
      Ast_c.info = {
      pinfo : parse_info;
      cocci_tag : (Ast_cocci.mcodekind * metavars_binding list) option ref;
      comments_tag : comments_around ref;
    }
    and il = info list
    and 'a wrap = 'a * il
    and 'a wrap2 = 'a * il
    and 'a wrap3 = 'a * il
    and name =
      Ast_c.name =
        RegularName of string wrap
      | CppConcatenatedName of string wrap wrap2 list
      | CppVariadicName of string wrap
      | CppIdentBuilder of string wrap * string wrap wrap2 list
    and fullType = typeQualifier * typeC
    and typeC = typeCbis wrap
    and typeCbis =
      Ast_c.typeCbis =
        BaseType of baseType
      | Pointer of fullType
      | Array of constExpression option * fullType
      | FunctionType of functionType
      | Enum of string option * enumType
      | StructUnion of structUnion * string option * structType
      | EnumName of string
      | StructUnionName of structUnion * string
      | TypeName of name * fullType option
      | ParenType of fullType
      | TypeOfExpr of expression
      | TypeOfType of fullType
    and baseType =
      Ast_c.baseType =
        Void
      | IntType of intType
      | FloatType of floatType
      | SizeType
      | SSizeType
      | PtrDiffType
    and intType = Ast_c.intType = CChar | Si of signed
    and signed = sign * base
    and base = Ast_c.base = CChar2 | CShort | CInt | CLong | CLongLong
    and sign = Ast_c.sign = Signed | UnSigned
    and floatType = Ast_c.floatType = CFloat | CDouble | CLongDouble
    and structUnion = Ast_c.structUnion = Struct | Union
    and structType = field list
    and field =
      Ast_c.field =
        DeclarationField of field_declaration
      | EmptyField of info
      | MacroDeclField of (string * argument wrap2 list) wrap
      | CppDirectiveStruct of cpp_directive
      | IfdefStruct of ifdef_directive
    and field_declaration =
      Ast_c.field_declaration =
        FieldDeclList of fieldkind wrap2 list wrap
    and fieldkind =
      Ast_c.fieldkind =
        Simple of name option * fullType
      | BitField of name option * fullType * info * constExpression
    and enumType = oneEnumType wrap2 list
    and oneEnumType = name * (info * constExpression) option
    and functionType = fullType * (parameterType wrap2 list * bool wrap)
    and parameterType =
      Ast_c.parameterType = {
      p_namei : name option;
      p_register : bool wrap;
      p_type : fullType;
    }
    and typeQualifier = typeQualifierbis wrap
    and typeQualifierbis =
      Ast_c.typeQualifierbis = {
      const : bool;
      volatile : bool;
    }
    and attribute = attributebis wrap
    and attributebis = Ast_c.attributebis = Attribute of string
    and expression = (expressionbis * exp_info ref) wrap3
    and exp_info = exp_type option * test
    and exp_type = fullType * local
    and local = Ast_c.local = LocalVar of parse_info | NotLocalVar
    and test = Ast_c.test = Test | NotTest
    and expressionbis =
      Ast_c.expressionbis =
        Ident of name
      | Constant of constant
      | FunCall of expression * argument wrap2 list
      | CondExpr of expression * expression option * expression
      | Sequence of expression * expression
      | Assignment of expression * assignOp * expression
      | Postfix of expression * fixOp
      | Infix of expression * fixOp
      | Unary of expression * unaryOp
      | Binary of expression * binaryOp * expression
      | ArrayAccess of expression * expression
      | RecordAccess of expression * name
      | RecordPtAccess of expression * name
      | SizeOfExpr of expression
      | SizeOfType of fullType
      | Cast of fullType * expression
      | StatementExpr of compound wrap
      | Constructor of fullType * initialiser wrap2 list
      | ParenExpr of expression
    and argument = (expression, weird_argument) Common.either
    and weird_argument =
      Ast_c.weird_argument =
        ArgType of parameterType
      | ArgAction of action_macro
    and action_macro = Ast_c.action_macro = ActMisc of il
    and constant =
      Ast_c.constant =
        String of (string * isWchar)
      | MultiString of string list
      | Char of (string * isWchar)
      | Int of (string * intType)
      | Float of (string * floatType)
    and isWchar = Ast_c.isWchar = IsWchar | IsChar
    and unaryOp =
      Ast_c.unaryOp =
        GetRef
      | DeRef
      | UnPlus
      | UnMinus
      | Tilde
      | Not
      | GetRefLabel
    and assignOp = Ast_c.assignOp = SimpleAssign | OpAssign of arithOp
    and fixOp = Ast_c.fixOp = Dec | Inc
    and binaryOp = Ast_c.binaryOp = Arith of arithOp | Logical of logicalOp
    and arithOp =
      Ast_c.arithOp =
        Plus
      | Minus
      | Mul
      | Div
      | Mod
      | DecLeft
      | DecRight
      | And
      | Or
      | Xor
    and logicalOp =
      Ast_c.logicalOp =
        Inf
      | Sup
      | InfEq
      | SupEq
      | Eq
      | NotEq
      | AndLog
      | OrLog
    and constExpression = expression
    and statement = statementbis wrap3
    and statementbis =
      Ast_c.statementbis =
        Labeled of labeled
      | Compound of compound
      | ExprStatement of exprStatement
      | Selection of selection
      | Iteration of iteration
      | Jump of jump
      | Decl of declaration
      | Asm of asmbody
      | NestedFunc of definition
      | MacroStmt
    and labeled =
      Ast_c.labeled =
        Label of name * statement
      | Case of expression * statement
      | CaseRange of expression * expression * statement
      | Default of statement
    and compound = statement_sequencable list
    and statement_sequencable =
      Ast_c.statement_sequencable =
        StmtElem of statement
      | CppDirectiveStmt of cpp_directive
      | IfdefStmt of ifdef_directive
      | IfdefStmt2 of ifdef_directive list * statement_sequencable list list
    and exprStatement = expression option
    and selection =
      Ast_c.selection =
        If of expression * statement * statement
      | Switch of expression * statement
    and iteration =
      Ast_c.iteration =
        While of expression * statement
      | DoWhile of statement * expression
      | For of exprStatement wrap * exprStatement wrap * exprStatement wrap *
          statement
      | MacroIteration of string * argument wrap2 list * statement
    and jump =
      Ast_c.jump =
        Goto of name
      | Continue
      | Break
      | Return
      | ReturnExpr of expression
      | GotoComputed of expression
    and asmbody = il * colon wrap list
    and colon = Ast_c.colon = Colon of colon_option wrap2 list
    and colon_option = colon_option_bis wrap
    and colon_option_bis =
      Ast_c.colon_option_bis =
        ColonMisc
      | ColonExpr of expression
    and declaration =
      Ast_c.declaration =
        DeclList of onedecl wrap2 list wrap
      | MacroDecl of (string * argument wrap2 list) wrap
    and onedecl =
      Ast_c.onedecl = {
      v_namei : (name * (info * initialiser) option) option;
      v_type : fullType;
      v_type_bis : fullType option ref;
      v_storage : storage;
      v_local : local_decl;
      v_attr : attribute list;
    }
    and storage = storagebis * bool
    and storagebis =
      Ast_c.storagebis =
        NoSto
      | StoTypedef
      | Sto of storageClass
    and storageClass = Ast_c.storageClass = Auto | Static | Register | Extern
    and local_decl = Ast_c.local_decl = LocalDecl | NotLocalDecl
    and initialiser = initialiserbis wrap
    and initialiserbis =
      Ast_c.initialiserbis =
        InitExpr of expression
      | InitList of initialiser wrap2 list
      | InitDesignators of designator list * initialiser
      | InitFieldOld of string * initialiser
      | InitIndexOld of expression * initialiser
    and designator = designatorbis wrap
    and designatorbis =
      Ast_c.designatorbis =
        DesignatorField of string
      | DesignatorIndex of expression
      | DesignatorRange of expression * expression
    and definition = definitionbis wrap
    and definitionbis =
      Ast_c.definitionbis = {
      f_name : name;
      f_type : functionType;
      f_storage : storage;
      f_body : compound;
      f_attr : attribute list;
      f_old_c_style : declaration list option;
    }
    and cpp_directive =
      Ast_c.cpp_directive =
        Define of define
      | Include of includ
      | Undef of string wrap
      | PragmaAndCo of il
    and define = string wrap * (define_kind * define_val)
    and define_kind =
      Ast_c.define_kind =
        DefineVar
      | DefineFunc of string wrap wrap2 list wrap
    and define_val =
      Ast_c.define_val =
        DefineExpr of expression
      | DefineStmt of statement
      | DefineType of fullType
      | DefineDoWhileZero of (statement * expression) wrap
      | DefineFunction of definition
      | DefineInit of initialiser
      | DefineText of string wrap
      | DefineEmpty
      | DefineTodo
    and includ =
      Ast_c.includ = {
      i_include : inc_file wrap;
      i_rel_pos : include_rel_pos option ref;
      i_is_in_ifdef : bool;
      i_content : (Common.filename * program) option;
    }
    and inc_file =
      Ast_c.inc_file =
        Local of inc_elem list
      | NonLocal of inc_elem list
      | Weird of string
    and inc_elem = string
    and include_rel_pos =
      Ast_c.include_rel_pos = {
      first_of : string list list;
      last_of : string list list;
    }
    and ifdef_directive =
      Ast_c.ifdef_directive =
        IfdefDirective of (ifdefkind * matching_tag) wrap
    and ifdefkind =
      Ast_c.ifdefkind =
        Ifdef
      | IfdefElseif
      | IfdefElse
      | IfdefEndif
    and matching_tag = Ast_c.matching_tag = IfdefTag of (int * int)
    and toplevel =
      Ast_c.toplevel =
        Declaration of declaration
      | Definition of definition
      | CppTop of cpp_directive
      | IfdefTop of ifdef_directive
      | MacroTop of string * argument wrap2 list * il
      | EmptyDef of il
      | NotParsedCorrectly of il
      | FinalDef of info
    and program = toplevel list
    and metavars_binding =
        (Ast_cocci.meta_name, metavar_binding_kind) Common.assoc
    and metavar_binding_kind =
      Ast_c.metavar_binding_kind =
        MetaIdVal of string * Ast_cocci.meta_name list
      | MetaFuncVal of string
      | MetaLocalFuncVal of string
      | MetaExprVal of expression * Ast_cocci.meta_name list
      | MetaExprListVal of argument wrap2 list
      | MetaParamVal of parameterType
      | MetaParamListVal of parameterType wrap2 list
      | MetaTypeVal of fullType
      | MetaInitVal of initialiser
      | MetaDeclVal of declaration
      | MetaFieldVal of field
      | MetaStmtVal of statement
      | MetaPosVal of (Ast_cocci.fixpos * Ast_cocci.fixpos)
      | MetaPosValList of (Common.filename * string * posl * posl) list
      | MetaListlenVal of int
    and comments_around =
      Ast_c.comments_around = {
      mbefore : Token_c.comment_like_token list;
      mafter : Token_c.comment_like_token list;
      mbefore2 : comment_and_relative_pos list;
      mafter2 : comment_and_relative_pos list;
    }
    and comment_and_relative_pos =
      Ast_c.comment_and_relative_pos = {
      minfo : Common.parse_info;
      mpos : int;
    }
    and comment = Common.parse_info
    and com = comment list ref
    val nullQualif : typeQualifierbis * 'a list
    val nQ : typeQualifierbis * 'a list
    val defaultInt : typeCbis
    val noType : unit -> ('a option * test) ref
    val noInstr : statementbis * 'a list
    val noTypedefDef : unit -> 'a option
    val emptyMetavarsBinding : metavars_binding
    val emptyAnnotCocci : Ast_cocci.mcodekind * metavars_binding list
    val emptyAnnot : (Ast_cocci.mcodekind * metavars_binding list) option
    val mcode_and_env_of_cocciref :
      (Ast_cocci.mcodekind * metavars_binding list) option ref ->
      Ast_cocci.mcodekind * metavars_binding list
    val emptyComments : comments_around
    val noRelPos : unit -> include_rel_pos option ref
    val noInIfdef : unit -> bool ref
    val no_virt_pos : Common.parse_info * int
    val fakeInfo : 'a -> info
    val noii : 'a list
    val noattr : 'a list
    val noi_content : (Common.filename * program) option
    val unwrap : 'a * 'b -> 'a
    val unwrap2 : 'a * 'b -> 'a
    val unwrap_expr : ('a * 'b) * 'c -> 'a
    val rewrap_expr : ('a * 'b) * 'c -> 'd -> ('d * 'b) * 'c
    val unwrap_typeC : 'a * ('b * 'c) -> 'b
    val rewrap_typeC : 'a * ('b * 'c) -> 'd -> 'a * ('d * 'c)
    val unwrap_typeCbis : 'a * 'b -> 'a
    val unwrap_st : 'a * 'b -> 'a
    val mk_e : 'a -> 'b -> ('a * ('c option * test) ref) * 'b
    val mk_e_bis : 'a -> 'b -> 'c -> ('a * 'b) * 'c
    val mk_ty : 'a -> 'b -> (typeQualifierbis * 'c list) * ('a * 'b)
    val mk_tybis : 'a -> 'b -> 'a * 'b
    val mk_st : 'a -> 'b -> 'a * 'b
    val get_ii_typeC_take_care : 'a * 'b -> 'b
    val get_ii_st_take_care : 'a * 'b -> 'b
    val get_ii_expr_take_care : 'a * 'b -> 'b
    val get_st_and_ii : 'a * 'b -> 'a * 'b
    val get_ty_and_ii : 'a * ('b * 'c) -> 'a * ('b * 'c)
    val get_e_and_ii : 'a * 'b -> 'a * 'b
    val get_type_expr : ('a * 'b ref) * 'c -> 'b
    val set_type_expr : ('a * 'b ref) * 'c -> 'b -> unit
    val get_onlytype_expr :
      ('a * (('b * 'c) option * 'd) ref) * 'e -> 'b option
    val get_onlylocal_expr :
      ('a * (('b * 'c) option * 'd) ref) * 'e -> 'c option
    val rewrap_str : string -> info -> info
    val rewrap_pinfo : parse_info -> info -> info
    val get_pi : parse_info -> Common.parse_info
    val get_opi : parse_info -> Common.parse_info
    val str_of_info : info -> string
    val get_info : (Common.parse_info -> 'a) -> info -> 'a
    val get_orig_info : (Common.parse_info -> 'a) -> info -> 'a
    val make_expanded : info -> info
    val pos_of_info : info -> int
    val opos_of_info : info -> int
    val line_of_info : info -> int
    val col_of_info : info -> int
    val file_of_info : info -> Common.filename
    val mcode_of_info : info -> Ast_cocci.mcodekind
    val pinfo_of_info : info -> parse_info
    val parse_info_of_info : info -> Common.parse_info
    val strloc_of_info : info -> string
    val is_fake : info -> bool
    val is_origintok : info -> bool
    type posrv =
      Ast_c.posrv =
        Real of Common.parse_info
      | Virt of virtual_position
    val compare_pos : info -> info -> int
    val equal_posl : int * int -> int * int -> bool
    val info_to_fixpos : info -> Ast_cocci.fixpos
    val is_test : expression -> bool
    val al_info : int -> info -> info
    val semi_al_info : info -> info
    val magic_real_number : int
    val real_al_info : info -> info
    val al_comments : comments_around -> comments_around
    val al_info_cpp : int -> info -> info
    val semi_al_info_cpp : info -> info
    val real_al_info_cpp : info -> info
    val split_comma : 'a wrap2 list -> ('a, il) Common.either list
    val unsplit_comma : ('a, il) Common.either list -> 'a wrap2 list
    val s_of_inc_file : inc_file -> string
    val s_of_inc_file_bis : inc_file -> string
    val fieldname_of_fieldkind : fieldkind -> name option
    val s_of_attr : (attributebis * 'a) list -> string
    val str_of_name : name -> string
    val get_s_and_ii_of_name : name -> string * il
    val get_s_and_info_of_name : name -> string * info
    val info_of_name : name -> info
    val ii_of_name : name -> il
    val get_local_ii_of_expr_inlining_ii_of_name :
      (expressionbis * 'a) * il -> il
    val get_local_ii_of_tybis_inlining_ii_of_name : typeCbis * il -> il
    val info_of_type : 'a * (typeCbis * il) -> parse_info
    val get_local_ii_of_st_inlining_ii_of_name :
      statementbis * info list -> info list
    val name_of_parameter : parameterType -> string option
  end
type ast_c_anything =
    Program of A.program
  | Toplevel of A.toplevel
  | Declaration of A.declaration
  | Definition of A.definition
  | Cpp_directive of A.cpp_directive
  | Ifdef_directive of A.ifdef_directive
  | Onedecl of A.onedecl
  | Name of A.name
  | Initialiser of A.initialiser
  | FullType of A.fullType
  | Initialiserbis of A.initialiserbis
  | Expression of A.expression
  | Definitionbis of A.definitionbis
  | FunctionType of A.functionType
  | Compound of A.compound
  | ParameterType of A.parameterType
  | Statement_sequencable of A.statement_sequencable
  | Statement of A.statement
  | Labeled of A.labeled
  | ExprStatement of A.exprStatement
  | Selection of A.selection
  | Iteration of A.iteration
  | Jump of A.jump
  | Expressionbis of A.expressionbis
  | Constant of A.constant
  | ArithOp of A.arithOp
  | AssignOp of A.assignOp
  | FixOp of A.fixOp
  | LogicalOp of A.logicalOp
  | UnaryOp of A.unaryOp
  | BinaryOp of A.binaryOp
  | TypeQualifier of A.typeQualifier
  | TypeCbis of A.typeCbis
  | ConstExpression of A.constExpression
  | BaseType of A.baseType
  | StructUnion of A.structUnion
  | StructType of A.structType
type qlp =
    Qdeclaration
  | Qfundefinition
  | Qinitialiser
  | Qname
  | Qlabeled
  | Qlabel
  | Qcase
  | Qcaserange
  | Qdefault
  | Qcompound
  | Qselection
  | Qif
  | Qswitch
  | Qiteration
  | Qwhile
  | Qdowhile
  | Qfor
  | Qjump
  | Qgoto
  | Qcontinue
  | Qbreak
  | Qreturn
  | Qgotocomputed
  | Qexpression
  | Qconstexpression
  | Qliteral
  | Qfuncall
  | Qcondexpr
  | Qsequence
  | Qassignment
  | Qprepostfix
  | Qunary
  | Qbinary
  | Qarrayaccess
  | Qrecordaccess
  | Qrecordptaccess
  | Qsizeof
  | Qsizeoftype
  | Qcast
  | Qref
  | Qgetref
  | Qderef
  | Qarith
  | Qunarith
  | Qunplus
  | Qunminus
  | Qdec
  | Qinc
  | Qdecorinc
  | Qplus
  | Qminus
  | Qmul
  | Qdiv
  | Qmod
  | Qdecleft
  | Qdecright
  | Qbitwise
  | Qtilde
  | Qbwand
  | Qbwor
  | Qxor
  | Qlogical
  | Qnot
  | Qand
  | Qor
  | Qcompare
  | Qinf
  | Qsup
  | Qinfeq
  | Qsupeq
  | Qeq
  | Qnoteq
  | Qpointer
  | Qarray
  | Qtypedef
  | Qbasetype
  | Qfuntype
  | Qvoid
  | Qsizetype
  | Qptrdifftype
  | Qsigned
  | Qunsigned
  | Qinttype
  | Qint
  | Qfloattype
  | Qchar
  | Qshort
  | Qfloat
  | Qlong
  | Qdouble
  | Qlongdouble
  | Qenum
  | Qstruct
  | Qunion
  | Qconst
  | Qvolatile
  | Qargument
  | Qtypeof
  | Qifdefdirective
  | Qifdef
  | Qifdefelseif
  | Qifdefelse
  | Qifdefendif
  | Qcppdirective
  | Qcppdefine
  | Qcppinclude
  | Qcppundef
  | Qcpppragmaandco
  | Qcppdefinevar
  | Qcppdefinefun
val mapToIndex : qlp -> int
val dimensions : int
