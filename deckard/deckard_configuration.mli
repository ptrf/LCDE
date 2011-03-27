module Cv :
  sig
    type charv = int list
    val vcreate : int -> charv
    val cvcreate : Deckard_types.qlp -> charv
    val ( +: ) : charv -> charv -> charv
    val vtokencount : charv -> int
    val vincr : charv -> int -> charv
    val cvincr : charv -> Deckard_types.qlp -> charv
    val vindex : charv -> int -> int
    val cvindex : charv -> Deckard_types.qlp -> int
  end
val create : Deckard_types.qlp -> Cv.charv
val nothing : 'a list
val vName : Cv.charv
val vLiteral : Cv.charv
val vDeclaration : Cv.charv
val vDefinition : Cv.charv
val vIfdefDirective : Cv.charv
val vIfdef : Cv.charv
val vIfdefElseif : Cv.charv
val vIfdefElse : Cv.charv
val vIfdefEndif : Cv.charv
val vCppDirective : Cv.charv
val vCppDefine : Cv.charv
val vCppInclude : Cv.charv
val vCppUndef : Cv.charv
val vCppPragmaAndCo : 'a list
val vCppDefineVar : Cv.charv
val vCppDefineFun : Cv.charv
val vInitialiser : Cv.charv
val vArgument : 'a list
val vLabeled : Cv.charv
val vCompound : 'a list
val vSelection : Cv.charv
val vIteration : Cv.charv
val vJump : Cv.charv
val vLabel : Cv.charv
val vCase : Cv.charv
val vCaseRange : Cv.charv
val vDefault : Cv.charv
val vIf : Cv.charv
val vSwitch : Cv.charv
val vWhile : Cv.charv
val vDoWhile : Cv.charv
val vFor : Cv.charv
val vGoto : Cv.charv
val vContinue : Cv.charv
val vBreak : Cv.charv
val vReturn : Cv.charv
val vGotoComputed : Cv.charv
val vExpression : Cv.charv
val vConstExpression : Cv.charv
val vFunCall : Cv.charv
val vCondExpr : Cv.charv
val vSequence : 'a list
val vAssignment : Cv.charv
val vPrePostfix : Cv.charv
val vUnary : Cv.charv
val vBinary : Cv.charv
val vArrayAccess : Cv.charv
val vRecordAccess : Cv.charv
val vRecordPtAccess : Cv.charv
val vSizeOf : Cv.charv
val vSizeOfType : Cv.charv
val vCast : Cv.charv
val vRef : Cv.charv
val vGetRef : Cv.charv
val vDeRef : Cv.charv
val vArith : Cv.charv
val vUnArith : Cv.charv
val vUnPlus : Cv.charv
val vUnMinus : Cv.charv
val vDec : Cv.charv
val vInc : Cv.charv
val vDecOrInc : Cv.charv
val vPlus : Cv.charv
val vMinus : Cv.charv
val vMul : Cv.charv
val vDiv : Cv.charv
val vMod : Cv.charv
val vDecLeft : Cv.charv
val vDecRight : Cv.charv
val vBitWise : Cv.charv
val vTilde : Cv.charv
val vBwAnd : Cv.charv
val vBwOr : Cv.charv
val vXor : Cv.charv
val vLogical : Cv.charv
val vNot : Cv.charv
val vAnd : Cv.charv
val vOr : Cv.charv
val vCompare : Cv.charv
val vInf : Cv.charv
val vSup : Cv.charv
val vInfEq : Cv.charv
val vSupEq : Cv.charv
val vEq : Cv.charv
val vNotEq : Cv.charv
val vPointer : Cv.charv
val vArray : Cv.charv
val vTypedef : Cv.charv
val vBaseType : Cv.charv
val vFunType : Cv.charv
val vVoid : Cv.charv
val vSizeType : Cv.charv
val vPtrDiffType : Cv.charv
val vSigned : Cv.charv
val vUnsigned : Cv.charv
val vIntType : Cv.charv
val vInt : Cv.charv
val vFloatType : Cv.charv
val vTypeOf : Cv.charv
val vChar : Cv.charv
val vShort : Cv.charv
val vFloat : Cv.charv
val vLong : Cv.charv
val vDouble : Cv.charv
val vLongDouble : Cv.charv
val vEnum : Cv.charv
val vStruct : Cv.charv
val vUnion : Cv.charv
val vConst : Cv.charv
val vVolatile : Cv.charv
