(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module A = Ast_c

(* TYPES TO COPE WITH COCCINELLE
 *
 * This
 *
 *)

type ast_c_anything =
    | Program of A.program
    | Toplevel of A.toplevel
    | Declaration of A.declaration
    | Definition of A.definition
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

(* type qlp: the q-level patterns
 *
 * The qlp type specificies the dimesions of the characteristic vectors along
 * with the mapToIndex function, which does the actual mapping to integer
 * dimensions. It should be thought of as a C enum.
 *
 * The qlp type contains all the different patterns, which may or may not be
 * used by the processing functions. As long as the vectors are uniformly
 * generated, it doesn't matter whether vectors are sparse or not.
 *
 * The processing functions in process.ml uses symbols defined in
 * deckard_configuration.ml. Each symbol correspond to 0 or more patterns
 * applied. So we might treat a do while as nothing; [], as a do while loop;
 * Cv.vcreate (mapToIndex Qdowhile), as a iteration; Cv.vcreate (mapToIndex
 * Qiteration) or even as both a iteration and a while loop;
 * (Cv.vcreate (mapToIndex Qwhile)) +: (Cv.vcreate (mapToIndex Qselection))
 *
 * So, by altering the symbols in the configuration module, we may alter the
 * vector generation.  *)

type qlp =
    (* toplevels *)
    | Qdeclaration
    | Qfundefinition
    (* declarations *)
    | Qinitialiser
    | Qname
    (* statements *)
    (* : labeled statements *)
    | Qlabeled
    | Qlabel
    | Qcase
    | Qcaserange
    | Qdefault
    (* : compounds *)
    | Qcompound
    (* : selections *)
    | Qselection
    | Qif
    | Qswitch
    (* : iterations *)
    | Qiteration
    | Qwhile
    | Qdowhile
    | Qfor
    (* : jump *)
    | Qjump
    | Qgoto
    | Qcontinue
    | Qbreak
    | Qreturn
    | Qgotocomputed
    (* expressions *)
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
    (* operators *)
    (* : references *)
    | Qref
    | Qgetref
    | Qderef
    (* : arithmetic *)
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
    (* : bitwise *)
    | Qbitwise
    | Qtilde
    | Qbwand
    | Qbwor
    | Qxor
    (* : logical *)
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
    (* types *)
    | Qpointer
    | Qarray
    | Qtypedef
    (* : basetypes *)
    | Qbasetype
    | Qfuntype
    | Qvoid
    | Qsizetype
    | Qptrdifftype
    (* : signed/unsigned *)
    | Qsigned
    | Qunsigned
    (* : int and float types *)
    | Qinttype
    | Qint
    | Qfloattype
    | Qchar
    | Qshort
    | Qfloat
    | Qlong
    | Qdouble
    | Qlongdouble
    (* : enums, structs, unions *)
    | Qenum
    | Qstruct
    | Qunion
    (* : typequalifiers *)
    | Qconst
    | Qvolatile
    | Qargument
    (* other *)
    | Qtypeof

let mapToIndex qlp =
    match qlp with
    | Qdeclaration      -> 1
    | Qfundefinition    -> 2
    | Qinitialiser      -> 3
    | Qname             -> 4
    | Qlabeled          -> 5
    | Qlabel            -> 6
    | Qcase             -> 7
    | Qcaserange        -> 8
    | Qdefault          -> 9
    | Qcompound         -> 10
    | Qselection        -> 11
    | Qif               -> 12
    | Qswitch           -> 13
    | Qiteration        -> 14
    | Qwhile            -> 15
    | Qdowhile          -> 16
    | Qfor              -> 17
    | Qjump             -> 18
    | Qcontinue         -> 19
    | Qbreak            -> 20
    | Qreturn           -> 21
    | Qgotocomputed     -> 22
    | Qexpression       -> 23
    | Qconstexpression  -> 24
    | Qliteral          -> 25
    | Qfuncall          -> 26
    | Qcondexpr         -> 27
    | Qsequence         -> 28
    | Qassignment       -> 29
    | Qprepostfix       -> 30
    | Qsizeoftype       -> 31
    | Qunary            -> 32
    | Qbinary           -> 33
    | Qarrayaccess      -> 34
    | Qrecordaccess     -> 35
    | Qrecordptaccess   -> 36
    | Qsizeof           -> 37
    | Qcast             -> 38
    | Qref              -> 39
    | Qgetref           -> 40
    | Qderef            -> 41
    | Qarith            -> 42
    | Qunarith          -> 43
    | Qunplus           -> 44
    | Qunminus          -> 45
    | Qdec              -> 46
    | Qinc              -> 47
    | Qdecorinc         -> 48
    | Qplus             -> 49
    | Qminus            -> 50
    | Qmul              -> 51
    | Qdiv              -> 52
    | Qmod              -> 53
    | Qdecleft          -> 54
    | Qdecright         -> 55
    | Qbitwise          -> 56
    | Qtilde            -> 57
    | Qbwand            -> 58
    | Qbwor             -> 59
    | Qxor              -> 60
    | Qlogical          -> 61
    | Qnot              -> 62
    | Qand              -> 63
    | Qor               -> 64
    | Qinf              -> 65
    | Qsup              -> 66
    | Qinfeq            -> 67
    | Qsupeq            -> 68
    | Qeq               -> 69
    | Qnoteq            -> 70
    | Qpointer          -> 71
    | Qarray            -> 72
    | Qtypedef          -> 73
    | Qbasetype         -> 74
    | Qvoid             -> 75
    | Qsizetype         -> 76
    | Qptrdifftype      -> 77
    | Qsigned           -> 78
    | Qunsigned         -> 79
    | Qinttype          -> 80
    | Qfloattype        -> 81
    | Qchar             -> 82
    | Qshort            -> 83
    | Qfloat            -> 84
    | Qlong             -> 85
    | Qdouble           -> 86
    | Qlongdouble       -> 87
    | Qenum             -> 88
    | Qstruct           -> 89
    | Qunion            -> 90
    | Qconst            -> 91
    | Qvolatile         -> 92
    | Qargument         -> 93
    | Qgoto             -> 94
    | Qfuntype          -> 95
    | Qtypeof           -> 96
    | Qint              -> 97
    | Qcompare          -> 98

(* ugly hack *)
let dimensions = 98

(* old qlp:

type qlp =
    (* prim exps *)
      Identifier
    | Literal       (* can be string literal or constant *)
    (* postfix expr *)
    | ArrayAcc
    | FunCall
    | DeRefOrRef      (* dereference or indirection *)
    | Member        (* struct/union member access *)
    (* unary expr *)
    | IncrOrDecr (* postfix and prefix *)
    | SizeOf
    | ArithmUnary   (* +, - *)
    | LogicUnary    (* !, ~ *)
    | Cast
    (* binary expr *)
    | Mult
    | Div
    | Mod
    | Add
    | Sub
    | Shift
    (* relational expr *)
    | Ineq          (* leq, geq, >, < *)
    | EqNeq         (* ==, != *)
    (* bitwise logic expr *)
    | BitAndOrXor   (* grouped together, maybe that ought to be changed.. see also
                       LogicUnary *)
    (* logical logic expr *)
    | LogAndOr      (* see also LogicUnary *)
    (* cond exp *)
    | CondExpOp (* .. ? .. : .. ; *)
    (* assignment *)
    | Assign
    | ArithAssign   (* += etc. *)
    | BitLogAssign  (* &= etc. *)
    | ShiftAssign   (* >>== etc. *)
    (* decl *)
    | Decl          (* doesn't distinguish between decl and decl with init *)
    | StructDecl    (* struct or union *)
    | EnumDecl
    (* types *)
    | Int
    | Float
    | Void
    | Char
    | EnumSpec
    | StructSpec    (* struct or union *)
    (* statements types *)
    | Compound      (* everything in blocks of { } ... maybe not a good idea *)
    | Select        (* if, if else, and switch *)
    | LabelCase     (* labels: and case LIT: *)
    | Iterate       (* while, do while, for *)
    | Jump          (* goto, continue, break, return *)


old mapToIndex

let mapToIndex qlp = match qlp with
      Identifier    -> 1
    | Literal       -> 2
    | ArrayAcc      -> 3
    | FunCall       -> 4
    | DeRefOrRef    -> 5
    | Member        -> 6
    | IncrOrDecr    -> 7
    | SizeOf        -> 8
    | ArithmUnary   -> 9
    | LogicUnary    -> 10
    | Cast          -> 11
    | Mult          -> 12
    | Div           -> 13
    | Mod           -> 14
    | Add           -> 15
    | Sub           -> 16
    | Shift         -> 17
    | Ineq          -> 18
    | EqNeq         -> 19
    | BitAndOrXor   -> 20
    | LogAndOr      -> 21
    | CondExpOp     -> 22
    | Assign        -> 23
    | ArithAssign   -> 24
    | BitLogAssign  -> 25
    | ShiftAssign   -> 26
    | Decl          -> 27
    | StructDecl    -> 28
    | EnumDecl      -> 29
    | Int           -> 30
    | Float         -> 31
    | Void          -> 32
    | Char          -> 33
    | EnumSpec      -> 34
    | StructSpec    -> 35
    | Compound      -> 36
    | Select        -> 37
    | LabelCase     -> 38
    | Iterate       -> 39
    | Jump          -> 40


let dimensions = 40
    *)

