(* for metavariables in general, but here because needed for metatypes *)
type inherited = bool (* true if inherited *)
type keep_binding = Unitary (* need no info *)
  | Nonunitary (* need an env entry *) | Saved (* need a witness *)

type meta_name = string * string (*Ast_cocci.meta_name*)

type typeC =
    ConstVol        of const_vol * typeC
  | BaseType        of baseType
  | SignedT         of sign * typeC option
  | Pointer         of typeC
  | FunctionPointer of typeC (* only return type *)
  | Array           of typeC (* drop size info *)
  | EnumName        of name
  | StructUnionName of structUnion * name
  | TypeName        of string
  | MetaType        of meta_name * keep_binding * inherited
  | Unknown (* for metavariables of type expression *^* *)

and name =
    NoName
  | Name of string
  | MV of meta_name * keep_binding * inherited

and tagged_string = string

and baseType = VoidType | CharType | ShortType | IntType | DoubleType
| FloatType | LongType | LongLongType | BoolType
| SizeType | SSizeType | PtrDiffType

and structUnion = Struct | Union

and sign = Signed | Unsigned

and const_vol = Const | Volatile

(* --------------------------------------------------------------------- *)
(* Printer *)
open Format

let rec type2c = function
    ConstVol(cv,ty) -> (const_vol cv) ^ (type2c ty)
  | BaseType(ty) -> baseType ty
  | SignedT(sgn,None) -> sign sgn
  | SignedT(sgn,Some ty) -> (sign sgn) ^ (type2c ty)
  | Pointer(ty) -> (type2c ty) ^ "*"
  | FunctionPointer(ty) -> (type2c ty) ^ "(*)(...)"
  | Array(ty) -> (type2c ty) ^ "[] "
  | EnumName(name) -> "enum " ^ (print_name name)
  | StructUnionName(kind,name) -> (structUnion kind) ^ (print_name name)
  | TypeName(name) -> name ^ " "
  | MetaType((rule,name),keep,inherited) -> name ^ " "
      (*
      let print_unitary = function
	  Unitary -> print_string "unitary"
	| Nonunitary -> print_string "nonunitary"
	| Saved -> print_string "saved" in
      print_string "/* ";
      print_string "keep:"; print_unitary keep;
      print_string " inherited:"; print_bool inherited;
      print_string " */"
      *)
  | Unknown -> "unknown "

and print_name = function
    NoName -> ""
  | MV ((_,name),_,_) -> name ^ " "
  | Name name -> name ^ " "

and baseType = function
    VoidType -> "void "
  | CharType -> "char "
  | ShortType -> "short "
  | IntType -> "int "
  | DoubleType -> "double "
  | FloatType -> "float "
  | LongType -> "long "
  | LongLongType -> "long long "
  | BoolType -> "bool "
  | SizeType -> "size_t "
  | SSizeType -> "ssize_t "
  | PtrDiffType -> "ptrdiff_t "


and structUnion = function
    Struct -> "struct "
  | Union -> "union "

and sign = function
    Signed -> "signed "
  | Unsigned -> "unsigned "

and const_vol = function
    Const -> "const "
  | Volatile -> "volatile "

let typeC t = print_string (type2c t)

(* t1 should be less informative than t1, eg t1 = Pointer(Unknown) and t2 =
Pointer(int) *)
(* only used in iso *)
(* needs to do something for MetaType *)
let compatible t1 = function
    None -> t1 = Unknown
  | Some t2 ->
      let rec loop = function
	  (Unknown,_) -> true
	| (ConstVol(cv1,ty1),ConstVol(cv2,ty2)) when cv1 = cv2 ->
	    loop(ty1,ty2)
	| (Pointer(ty1),Pointer(ty2)) -> loop(ty1,ty2)
	| (FunctionPointer(ty1),_) -> false (* not enough info *)
	| (_,FunctionPointer(ty2)) -> false (* not enough info *)
	| (Array(ty1),Array(ty2)) -> loop(ty1,ty2)
	| (_,_) -> t1=t2 in
      loop (t1,t2)
