(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

module A = Ast_c

(*  Encapsulate *)

type ast_c_anything =
    | Declaration of A.declaration
    | Definition of A.definition
    | Cpp_directive of A.cpp_directive
    | Ifdef_directive of A.ifdef_directive
    | Expression of A.expression
    | Statement of A.statement

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
    (* preprocessor stuff *)
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

let mapToIndex qlp =
    match qlp with
    | Qdeclaration      ->   1
    | Qfundefinition    ->   2
    | Qinitialiser      ->   3
    | Qname             ->   4
    | Qlabeled          ->   5
    | Qlabel            ->   6
    | Qcase             ->   7
    | Qcaserange        ->   8
    | Qdefault          ->   9
    | Qcompound         ->  10
    | Qselection        ->  11
    | Qif               ->  12
    | Qswitch           ->  13
    | Qiteration        ->  14
    | Qwhile            ->  15
    | Qdowhile          ->  16
    | Qfor              ->  17
    | Qjump             ->  18
    | Qcontinue         ->  19
    | Qbreak            ->  20
    | Qreturn           ->  21
    | Qgotocomputed     ->  22
    | Qexpression       ->  23
    | Qconstexpression  ->  24
    | Qliteral          ->  25
    | Qfuncall          ->  26
    | Qcondexpr         ->  27
    | Qsequence         ->  28
    | Qassignment       ->  29
    | Qprepostfix       ->  30
    | Qsizeoftype       ->  31
    | Qunary            ->  32
    | Qbinary           ->  33
    | Qarrayaccess      ->  34
    | Qrecordaccess     ->  35
    | Qrecordptaccess   ->  36
    | Qsizeof           ->  37
    | Qcast             ->  38
    | Qref              ->  39
    | Qgetref           ->  40
    | Qderef            ->  41
    | Qarith            ->  42
    | Qunarith          ->  43
    | Qunplus           ->  44
    | Qunminus          ->  45
    | Qdec              ->  46
    | Qinc              ->  47
    | Qdecorinc         ->  48
    | Qplus             ->  49
    | Qminus            ->  50
    | Qmul              ->  51
    | Qdiv              ->  52
    | Qmod              ->  53
    | Qdecleft          ->  54
    | Qdecright         ->  55
    | Qbitwise          ->  56
    | Qtilde            ->  57
    | Qbwand            ->  58
    | Qbwor             ->  59
    | Qxor              ->  60
    | Qlogical          ->  61
    | Qnot              ->  62
    | Qand              ->  63
    | Qor               ->  64
    | Qinf              ->  65
    | Qsup              ->  66
    | Qinfeq            ->  67
    | Qsupeq            ->  68
    | Qeq               ->  69
    | Qnoteq            ->  70
    | Qpointer          ->  71
    | Qarray            ->  72
    | Qtypedef          ->  73
    | Qbasetype         ->  74
    | Qvoid             ->  75
    | Qsizetype         ->  76
    | Qptrdifftype      ->  77
    | Qsigned           ->  78
    | Qunsigned         ->  79
    | Qinttype          ->  80
    | Qfloattype        ->  81
    | Qchar             ->  82
    | Qshort            ->  83
    | Qfloat            ->  84
    | Qlong             ->  85
    | Qdouble           ->  86
    | Qlongdouble       ->  87
    | Qenum             ->  88
    | Qstruct           ->  89
    | Qunion            ->  90
    | Qconst            ->  91
    | Qvolatile         ->  92
    | Qargument         ->  93
    | Qgoto             ->  94
    | Qfuntype          ->  95
    | Qtypeof           ->  96
    | Qint              ->  97
    | Qcompare          ->  98
    | Qifdefdirective   ->  99
    | Qifdef            -> 100
    | Qifdefelseif      -> 101
    | Qifdefelse        -> 102
    | Qifdefendif       -> 103
    | Qcppdirective     -> 104
    | Qcppdefine        -> 105
    | Qcppinclude       -> 106
    | Qcppundef         -> 107
    | Qcpppragmaandco   -> 108
    | Qcppdefinevar     -> 109
    | Qcppdefinefun     -> 110

(* ugly hack *)
let dimensions = 110
