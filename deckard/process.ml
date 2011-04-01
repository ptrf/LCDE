(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

(* process.ml
 *
 * The Process module contains functions to traverse the tree and create
 * vectors.
 *)

open Deckard_configuration
open Common
open Ast_c
open Infixes

module Dt = Deckard_types
module C = Context
module Cv = Charv

(* hacks *)
let filename = ref ""


(*
 * SHORTHANDS
 *)

(* store, store_mergeable
 *
 * We use store to save a characteristic vector and a reference to the
 * corresponding node.
 * We use store_mergeable when we want to store a characteristic vector for a
 * node deemed mergeable
 *
 * In the case of store_mergeable, level is information of the mergeability
 * level, i.e. global declarations and function definitions are on level 0,
 * statements in a function body are on level 1, statements in loops etc are on
 * level 2 or below.
 *)

let store e v =
    C.vstore := (v,e) :: !C.vstore

let store_mergeable level e v =
    (if level <> 0 then C.vseq := (!filename,((v,e),level)) :: !C.vseq);
    store [e] v

(* symbols
 *
 * As this is incomplete code (we don't yet support all gcc extensions, etc.)
 * these shorthands are used with failwith when we meet special cases
 *)

let debug_implthis s = "if this is encountered, this case should be implemented. encountered in " ^ s
let debug_sadv = "seek advice. this is a special case!"


(*
 * PROCESSING FUNCTIONS
 *)

(* pname, pliteral
 *
 * We don't care to distinguish among names and literals, but others might.
 *
 * beware that pname is called with both names and strings.
 *)

let pliteral _ = vLiteral
let pname _ = vName


(* TOPLEVEL *)

(* pprogram - entry point
 *
 * pprogram is an entrypoint and starts the post order pass on the tree,
 * generating vectors
 *
 *)

let rec pprogram tls =
    (* this might fail spectacularly - beware *)
    let hd = List.hd tls in
    filename := (Ast_c.file_of_info (List.hd (Lib_parsing_c.ii_of_toplevel
    hd)));
    List.iter ptoplevel tls

(* ptoplevel
 *
 * Invoked by list iteration, so we discard any returns.
 *)

and ptoplevel toplevel =
    let level = 1 in
    match toplevel with
    | Declaration (decl) ->
            let _ = pdeclaration level decl in
            ()
    | Definition (def) ->
            let _ = pdefinition level def in
            ()
    | CppTop c ->
            let _ = pcpptop level c in
            ()
    | IfdefTop i ->
            let _ = pifdeftop level i in
            ()
    | MacroTop (m,_,_) ->
            pmacrotop level m;
            ()
    (* the following only contains info stuff - NotParsedCorrectly probably out
     * to emit some warning of sorts *)
    | FinalDef _ | EmptyDef _ | NotParsedCorrectly _ -> ()

(* CPP *)

(* pcpptop, pcppdefine, pcppdefineval
 *)

and pcpptop level directive =
    let v_dir = (match directive with
    | Define d -> vCppDefine +: (pcppdefine d)
    | Include _ -> vCppInclude
    | Undef _ -> vCppUndef
    | PragmaAndCo _ -> vCppPragmaAndCo) in
    let v = v_dir +: vCppDirective in
    store_mergeable level (Dt.Cpp_directive directive) v;
    v

and pcppdefine = fun (_,(kind,value)) ->
    let v_k = (match kind with
        | DefineVar -> vCppDefineVar
        | DefineFunc _ -> vCppDefineFun
    ) in
    let v_v = pcppdefineval value in
    v_v +: v_k

and pcppdefineval v =
    match v with
    | DefineExpr e -> (pexpr e)
    | DefineStmt s -> (pstatement 0 s)
    | DefineType t -> (pfullType t)
    | DefineDoWhileZero ((s, e),_) ->
            (pstatement 0 s) +: (pexpr e)
    | DefineFunction d -> (pdefinition 0 d)
    | DefineInit i -> (pinitialiser i)
    | DefineText _ | DefineEmpty | DefineTodo -> nothing

(* pifdeftop, pifdefkind
 *)

and pifdeftop level directive =
    let v_ifdef = (match directive with
    | IfdefDirective ((kind,_),_) ->
            pifdefkind kind
    ) in
    let v = v_ifdef +: vIfdefDirective in
    store_mergeable level (Dt.Ifdef_directive directive) v;
    v

and pifdefkind kind =
    match kind with
    | Ifdef -> vIfdef
    | IfdefElseif -> vIfdefElseif
    | IfdefElse -> vIfdefElse
    | IfdefEndif -> vIfdefEndif

(* pmacrotop
 *)

and pmacrotop _ _ =
    ()

(* DECLARATIONS *)

(* pdeclaration
 *
 * Declarations are packed together as Lists or as MacroDecls.
 * Depending on which one, we treat them differently.
 * More concrete documentation pending TODO
 *
 * (Find out how decllists work, i.e. what does a onedecl correspond to codewise
 * compared to a decllist. - Q is where to store vectors, etc.)
 *
 *)
and pdeclaration level decl =
    let decl_packed = Dt.Declaration decl in
    match decl with
    | DeclList (decls,_) ->
            let v = List.fold_left
                    (fun x y ->
                        x +: (ponedecl (fst y)))
                    nothing decls
            in
            (* if we are called from toplevel, we save our vector, else we let
             * pstatement save it for us *)
            if level = 1 then store_mergeable level decl_packed v;
            v
            (* List.fold_ (fun x -> ponedecl level (fst x)) decls*)
    | MacroDecl _ -> failwith (debug_implthis "pdeclaration")

(* ponedecl
 *
 * Invoked for individual declarations in DeclLists.
 *
 * More concrete documentation pending.
 *)
and ponedecl decl =
    let extract_init iopt = match iopt with
        | None -> None
        | Some (_,opt) -> Some opt
    in
    let name_and_init = match decl.v_namei with
        | None -> None (* failwith (debug_sadv ^ " ||   " ^ (Dumper.dump decl))*)
        | Some (n,i) -> Some (n, extract_init i)
    in
    let v_name_and_init = match name_and_init with
        | None -> nothing
        | Some (n,None) -> pname n
        | Some (n,Some i) -> let v_init = pinitialiser i in
                             v_init +: (pname n)
    in
    let v_type = pfullType decl.v_type in
    let v = vDeclaration +: v_type +: v_name_and_init in
    v

(* pinitialiser
 *
 * Process initialisers from declarations.
 *)
and pinitialiser = fun (initialiserbis, _) ->
    match initialiserbis with
    | InitExpr (e) ->
            pexpr e
    | InitList xs ->
            List.fold_left (fun x y -> x +:
                            (pinitialiser (fst y))) nothing xs
    | InitDesignators _ | InitFieldOld _ | InitIndexOld _ ->
            failwith (debug_implthis "pinitialiser")


(* EXPRESSIONS *)

(* pexpr, pconstexpr
 *
 * NOTE: Postfix and Infix (sic; Prefix) operators (++ and --)
 * are handled as the same.
 *)
and pconstexpr expr =
    vConstExpression +: (pexpr expr)

and pexpr expression =
    let expr = fst (fst expression) in
    match expr with
    | Ident (name) -> pname name
    | Constant (c) -> pliteral c
    | FunCall (e, args) ->
            let v_expr = pexpr e in
            let v_args = pargument args in
            vFunCall +: v_expr +: v_args
    | CondExpr (e1, e2, e3) ->
            let v_e1 = pexpr e1 in
            let v_e2 = match e2 with
            | Some e -> pexpr e
            | None -> nothing
            in
            let v_e3 = pexpr e3 in
            vCondExpr +: v_e1 +: v_e2 +: v_e3
    | Sequence (e1,e2) ->
            let v_e1 = pexpr e1 in
            let v_e2 = pexpr e2 in
            vSequence +: v_e1 +: v_e2
    | Assignment (e1, op, e2) ->
            let v_e1 = pexpr e1 in
            let v_e2 = pexpr e2 in
            (* vAssignment *)
            let v_op = passignOp op in
            v_e1 +: v_e2 +: v_op
    | Postfix (e, _) | Infix (e, _) ->
            let v_e = pexpr e in
            vPrePostfix +: v_e
    | Unary (e, op) ->
            let v_e = pexpr e in
            let v_op = punaryOp op in
            vUnary +: v_e +: v_op
    | Binary (e1, op, e2) ->
            let v_e1 = pexpr e1 in
            let v_e2 = pexpr e2 in
            let v_op = pbinaryOp op in
            vBinary +: v_e1 +: v_e2 +: v_op
    | ArrayAccess (e1,e2) ->
            let v_e1 = pexpr e1 in
            let v_e2 = pexpr e2 in
            vArrayAccess +: v_e1 +: v_e2
    | RecordAccess (e, name) ->
            let v_e = pexpr e in
            let v_name = pname name in
            vRecordAccess +: v_name +: v_e
    | RecordPtAccess (e, name) ->
            let v_e = pexpr e in
            let v_name = pname name in
            vRecordPtAccess +: v_e +: v_name
    | SizeOfExpr (e) ->
            let v_e = pexpr e in
            vSizeOf +: v_e
    | SizeOfType (t) ->
            let v_t = pfullType t in
            vSizeOfType +: v_t
    | Cast (t, e) ->
            let v_t = pfullType t in
            let v_e = pexpr e in
            vCast +: v_t +: v_e
    | StatementExpr _ -> failwith (debug_implthis "pexpr - stmtexpr " ^
    (Dumper.dump expression))
    | Constructor _ ->  failwith (debug_implthis "pexpr - constructor " ^
    (Dumper.dump expression))
    | ParenExpr e -> pexpr e

(* pargument
 *
 * Arguments to function calls are processed here.
 * NOTE: Arguments can be complex expression, but are not deemed worthy of
 * saving. You may want to revise this decision.
 *)
and pargument argis =
    let parg e_or_wa = match e_or_wa with
        | Left (e) ->
                vArgument +: (pexpr e)
        | Right _ ->
                failwith (debug_implthis "pargument")
    in
    List.fold_left (fun x y -> x +: (parg (fst y))) nothing argis


(* OPERATORS *)

(* passignOp
 *
 * Assignment operators.
 *
 * NOTE: To avoid further qlp bloat, x <op>= a is treated as the semantically
 * identical (right?) x = x op a.
 *
 *)

and passignOp op =
    match op with
    | SimpleAssign -> vAssignment
    | OpAssign aop -> vAssignment +: parithOp aop

and punaryOp op = match op with
    | GetRef        -> vGetRef
    | DeRef         -> vDeRef
    | UnPlus        -> vUnPlus
    | UnMinus       -> vUnMinus
    | Tilde         -> vTilde +: vBitWise
    | Not           -> vNot +: vLogical
    | GetRefLabel   -> failwith (debug_implthis "punaryOp")

and pbinaryOp op = match op with
    | Arith (op) -> parithOp op
    | Logical (op) -> plogicalOp op

and parithOp op = match op with
    | Plus      -> vPlus
    | Minus     -> vMinus
    | Mul       -> vMul
    | Div       -> vDiv
    | Mod       -> vMod
    | DecLeft   -> vDecLeft
    | DecRight  -> vDecRight
    | And       -> vBwAnd +: vBitWise
    | Or        -> vBwOr +: vBitWise
    | Xor       -> vXor +: vBitWise

and plogicalOp op = match op with
    | Inf    -> vInf +: vCompare
    | Sup    -> vSup +: vCompare
    | SupEq  -> vSupEq +: vCompare
    | InfEq  -> vInfEq +: vCompare
    | Eq     -> vEq +: vCompare
    | NotEq  -> vNotEq +: vCompare
    | AndLog -> vAnd +: vLogical
    | OrLog  -> vOr +: vLogical


(* FUNCTION DEFINITIONS *)

(* pdefinition
 *
 * Function definitions are processed by pdefinition.
 *
 * NOTE: Take care if code is adapted to support nested function definitions
 *)

and pdefinition level definition =
    let def_packed = Dt.Definition definition in
    let fundef = fst definition in
    let v_name = pname (fundef.f_name) in
    let v_type = pfunctionType (fundef.f_type) in
    let v_body = pcompound (level+1) (fundef.f_body) in
    match (fundef.f_old_c_style) with
    | Some _ -> failwith (debug_implthis "pdefinition")
    | None ->
            let v = vDefinition +: v_name +: v_type +: v_body in
            store_mergeable level def_packed v;
            v

(* pfunctionType
 *
 * function types are the types of their arguments and their return type.
 *)
and pfunctionType = fun (fullType, (parameters,_)) ->
    let v_type = pfullType fullType in
    let v_params = List.fold_left (fun x y ->
        x +: (pparameterType (fst y))) nothing parameters in
    v_type +: v_params +: vFunType

and pparameterType param =
    let v_name = match (param.p_namei) with
        | Some n -> pname n
        | None -> nothing
    in
    let v_type = pfullType (param.p_type) in
    v_type +: v_name

(* STATEMENTS *)

(* pstatement
 *
 * The statement type is an away recursive or nested, as a statement can contain
 * a compound, which in itself contains a list of statements, etc. Vectors for
 * all statements, whether 'nested' or not are generated and saved. In
 * subsequent phases, overlapping code clones are pruned.
 *
 * Mergeability is handled like this: Everytime we meet something that's neither
 * a jump nor a exprStatement, we increment the level parameter and pass it
 * recursively. That way, we delay the merging decisions to a later merging
 * phase, enabling us to focus on vector generation here.
 *
 *)

and pstatement level statement =
    let statement_packed = Dt.Statement statement in
    let statementbis = fst statement in
    let newlevel = if level <> 0 then level+1 else level in
    let v = (
        match statementbis with
        | Labeled (l) -> (plabeled newlevel l) +: vLabeled
        | Compound (c) -> (pcompound newlevel c) +: vCompound
        | ExprStatement (e) -> (pexprStatement e)
        | Selection (s) -> (pselection newlevel s) +: vSelection
        | Iteration (i) -> (piteration newlevel i) +: vIteration
        | Jump (j) -> (pjump j) +: vJump
        | Decl (d) -> (pdeclaration newlevel d)
        | Asm _ | NestedFunc _ | MacroStmt -> failwith (debug_implthis
        "pstatement")
    )
    in
    store_mergeable level statement_packed v;
    v


(* plabeled, pjump, pexprStatement, pselection, pcompound, piteration
 *
 * Characteristic vectors for these are returned from these functions.
 * pstatement handles all saving of vectors on this level.
 *
 * TODO More elaborate documentation :)
 *)

and plabeled newlevel labeled =
    match labeled with
    | Label (n,s) -> vLabel +: (pname n) +: (pstatement newlevel s)
    | Case (e,s) -> vCase +: (pexpr e) +: (pstatement newlevel s)
    | CaseRange (e1,e2,s) ->
            let v_e1 = pexpr e1 in
            let v_e2 = pexpr e2 in
            let v_s = pstatement newlevel s in
            vCaseRange +: v_s +: v_e1 +: v_e2
    | Default (s) -> vDefault +: (pstatement newlevel s)

and pjump jump =
    match jump with
    | Goto (n) -> vGoto +: (pname n)
    | Continue -> vContinue
    | Break -> vBreak
    | Return -> vReturn
    | ReturnExpr (e) -> (pexpr e) +: vReturn
    | GotoComputed (e) -> (pexpr e) +: vGoto

and pexprStatement exproption =
    match exproption with
   | Some (e) -> pexpr e
   | None -> nothing

and pselection newlevel selection =
    match selection with
    | If (e,s1,s2) ->
            let v_if = vIf +: (pexpr e) in
            let v_s1 = pstatement newlevel s1 in
            let v_s2 = pstatement newlevel s2 in
            let v = v_if +: v_s1 +: v_s2 in
            v
    | Switch (e,s) ->
            let v_e = (pexpr e) in
            let v_s1 = pstatement newlevel s in
            v_e +: v_s1 +: vSwitch

and pcompound newlevel statement_sequencables =
    let pst_sq st_sq = match st_sq with
        | StmtElem (s) -> pstatement newlevel s
        | CppDirectiveStmt s -> (pcpptop newlevel s)
        | IfdefStmt i -> pifdeftop newlevel i
        | IfdefStmt2 _ -> failwith
        (debug_implthis "pcompound")
    in
    List.fold_left (fun x y -> x +: (pst_sq y)) nothing statement_sequencables

and piteration newlevel iteration =
    match iteration with
    | While (e,s) ->
            let v_e = pexpr e in
            let v_s = pstatement newlevel s in
            vWhile +: v_e +: v_s
    | DoWhile (s,e) ->
            let v_e = pexpr e in
            let v_s = pstatement newlevel s in
            vDoWhile +: v_e +: v_s
    | For ((es1,_),(es2,_),(es3,_),s) ->
            let v_es1 = pexprStatement es1 in
            let v_es2 = pexprStatement es2 in
            let v_es3 = pexprStatement es3 in
            let v_s = pstatement newlevel s in
            vFor +: v_es1 +: v_es2 +: v_es3 +: v_s
    | MacroIteration _ -> failwith (debug_implthis "piteration")


(* type *)

and pfullType fulltype =
    let q = fst fulltype in
    let t = fst (snd fulltype) in
    (ptypeCbis t) +: (ptypeQualifier q)

and ptypeQualifier = fun (q,_) ->
    let v_c = if q.const = true then vConst else nothing in
    let v_v = if q.volatile = true then vVolatile else nothing in
    v_v +: v_c

and ptypeCbis t =
    match t with
    | BaseType (b) ->
            (pbaseType b) +: vBaseType
    | Pointer (f) ->
            (pfullType (f)) +: vPointer
    | Array (cEo, f) ->
            let v_ce = (match cEo with | Some (e) -> pconstexpr e | None -> nothing) in
            v_ce +: (pfullType f) +: vArray
    | FunctionType (fT)->
            (pfunctionType fT) (* vFunType is added at pfunctionType *)
    (* should we do something with the string in the enum, structs and unions?
     * *)
    | Enum (_, eT) ->
            (penumType eT) +: vEnum
    | StructUnion (sU, s, sT) ->
            (pname s) +: (pstructUnion sU) +: (pstructType sT)
    | EnumName (s) ->
            (pname s) +: vEnum
    | StructUnionName (sU,s) ->
            (pstructUnion sU) +: (pname s)
    | TypeName (n, f) ->
            (pname n) +: (match f with | Some (ft) -> pfullType ft | None ->
                nothing )
    | ParenType (t) -> pfullType t
            (*failwith (debug_sadv ^ " || " ^ (Dumper.dump lol))*)
    | TypeOfExpr (e) ->
            (pexpr e) +: vTypeOf
    | TypeOfType (t) ->
            let v_type = pfullType t in
            v_type +: vTypeOf

and pstructUnion su =
    match su with
    | Struct -> vStruct
    | Union -> vUnion

and pstructType s =
    List.fold_left (fun x y -> x +: (pfield y)) nothing s

and pfield field =
    match field with
    | DeclarationField decl ->
            pdeclfield decl
    | EmptyField _ | MacroDeclField _ | CppDirectiveStruct _ | IfdefStruct _ ->
            failwith (debug_implthis "pfield")

and pdeclfield decl =
    match decl with
    | FieldDeclList (decls,_) ->
            List.fold_left (fun x y -> x +: (pfieldkind (fst y))) nothing decls

and pfieldkind f =
    match f with
    | Simple (n,t) ->
            let v_name = (match n with | Some n -> pname n | None -> nothing) in
            v_name +: (pfullType t)
    | BitField (n,t,_,cE) ->
            let v_name = (match n with | Some n -> pname n | None -> nothing) in
            v_name +: (pfullType t) +: (pconstexpr cE)

and pbaseType b =
    match b with
    | Void -> vVoid
    | SizeType -> vSizeType
    | SSizeType -> vSizeType
    | PtrDiffType -> vPtrDiffType
    | IntType it -> vIntType +: (pintType it)
    | FloatType ft -> vFloatType +: (pfloatType ft)

and pintType t =
    match t with
    | CChar -> vChar
    | Si si -> psigned si

and penumType e = List.fold_left (fun x y -> x +: (poneEnumType (fst y))) nothing e

and poneEnumType y =
    let v_e = (match (snd y) with
                | None -> nothing
                | Some (_,cE) -> (pconstexpr cE))
    in
    v_e +: (pname (fst y))

and psigned s =
    let v_s = (match (fst s) with | Signed -> vSigned | UnSigned -> vUnsigned) in
    let v_b = (match (snd s) with | CChar2 -> vChar
                                  | CShort -> vShort
                                  | CInt -> vInt
                                  | CLong -> vLong
                                  | CLongLong -> failwith (debug_implthis
                                  "psigned"))
    in
    v_s +: v_b

and pfloatType f =
    match f with
    | CFloat -> vFloat
    | CDouble -> vDouble
    | CLongDouble -> vLongDouble
