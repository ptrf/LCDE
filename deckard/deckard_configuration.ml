(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* deckard_configuration.ml
 *
 * Uses the Deckard_types and Charv modules, as this code specifices symbols for
 * vector creation
 *)

open Deckard_types
module Cv = Charv


(* Deckard Configuration - Rationale:
 *
 * These symbols provide control over how vectors are generated by the process
 * module.
 *
 * Whenever a "Foo" construct is processed, the corresponding symbol "vFoo" is
 * used to generate the vector for that subtree.  So changing the symbols
 * changes what vectors the Process module creates.
 *
 * A sensible example: You might want to treat DoWhile and While loops
 * differently or not. In the first case you could let vDoWhile = create
 * Qdowhile and vWhile = create Qwhile. In the other case, you could let
 * vDoWhile = create Qiteration and vWhile = create Qiteration.
 *
 * Beware: This symbol list is not exhaustive. Symbols may be added, when more
 * constructors are added.
 *)

(* Standard Configuration
 *
 * This is the standard configuration. Depending on the use, you might want to
 * change this
 *
 * TODO
 *)

(* shorthands for making out lives easier *)
let create qlp = Cv.cvcreate qlp
let nothing = []

(* generic constructs *)
let vName = create Qname
let vLiteral = create Qliteral

(* toplevel constructs *)
let vDeclaration = create Qdeclaration
let vDefinition = create Qfundefinition

(* declarations constructs *)
let vInitialiser = create Qinitialiser

let vArgument = nothing

(* statement constructs *)
let vLabeled = create Qlabeled
let vCompound = nothing
let vSelection = create Qselection
let vIteration = create Qiteration
let vJump = create Qjump

(* labeled constructs *)
let vLabel = create Qlabel
let vCase = create Qcase
let vCaseRange = create Qcaserange
let vDefault = create Qdefault

(* selection constructs *)
let vIf = create Qif
let vSwitch = create Qswitch

(* iterations constructs *)
let vWhile = create Qwhile
let vDoWhile = create Qdowhile
let vFor = create Qfor

(* jump constructs *)
let vGoto = create Qgoto
let vContinue = create Qcontinue
let vBreak = create Qbreak
let vReturn = create Qreturn
let vGotoComputed = create Qgotocomputed

(* expression constructs *)
let vExpression = create Qexpression
let vConstExpression = create Qconstexpression
let vFunCall = create Qfuncall
let vCondExpr = create Qcondexpr
let vSequence = nothing
let vAssignment = create Qassignment

let vPrePostfix = create Qprepostfix
let vUnary = create Qunary
let vBinary = create Qbinary
let vArrayAccess = create Qarrayaccess
let vRecordAccess = create Qrecordaccess
let vRecordPtAccess = create Qrecordptaccess
let vSizeOf = create Qsizeof
let vSizeOfType = create Qsizeoftype
let vCast = create Qcast
let vRef = create Qref
let vGetRef = create Qgetref
let vDeRef = create Qderef

(* arithmetic operations *)
let vArith = create Qarith
let vUnArith = create Qunarith
let vUnPlus = create Qunplus
let vUnMinus = create Qunminus
let vDec = create Qdec
let vInc = create Qinc
let vDecOrInc = create Qdecorinc
let vPlus = create Qplus
let vMinus = create Qminus
let vMul = create Qmul
let vDiv = create Qdiv
let vMod = create Qmod
let vDecLeft = create Qdecleft
let vDecRight = create Qdecright

(* bitwise operations *)
let vBitWise = create Qbitwise
let vTilde = create Qtilde
let vBwAnd = create Qbwand
let vBwOr = create Qbwor
let vXor = create Qxor

(* logical operations *)
let vLogical = create Qlogical
let vNot = create Qnot
let vAnd = create Qand
let vOr = create Qor

(* comparisions *)
let vCompare = create Qcompare
let vInf = create Qinf
let vSup = create Qsup
let vInfEq = create Qinfeq
let vSupEq = create Qsupeq
let vEq = create Qeq
let vNotEq = create Qnoteq

(* type characteristics *)
let vPointer = create Qpointer
let vArray = create Qarray
(* - currently not used *)
let vTypedef = create Qtypedef
let vBaseType = create Qbasetype
let vFunType = create Qfuntype
let vVoid = create Qvoid
(* - used for both SSizeType and SizeType *)
let vSizeType = create Qsizetype
let vPtrDiffType = create Qptrdifftype
let vSigned = create Qsigned
let vUnsigned = create Qunsigned
let vIntType = create Qinttype
let vInt = create Qint
let vFloatType = create Qfloattype
let vTypeOf = create Qtypeof
let vChar = create Qchar
let vShort = create Qshort
let vFloat = create Qfloat
let vLong = create Qlong
let vDouble = create Qdouble
let vLongDouble = create Qlongdouble
let vEnum = create Qenum
let vStruct = create Qstruct
let vUnion = create Qunion

(* type qualifiers *)
let vConst = create Qconst
let vVolatile = create Qvolatile


