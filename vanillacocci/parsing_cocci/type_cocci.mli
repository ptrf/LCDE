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

val type2c : typeC -> string
val typeC : typeC -> unit

val compatible : typeC -> typeC option -> bool
