type sequence =
    Seq of element * sequence
  | Empty
  | SExists of Ast_cocci.meta_name * sequence

and term =
    Atomic of Ast_cocci.rule_elem
  | IfThen of term * term * Ast_cocci.end_info
  | TExists of Ast_cocci.meta_name * term

and element =
    Term of term * dots_bef_aft
  | Or of sequence * sequence
  | DInfo of dots
  | EExists of Ast_cocci.meta_name * element

and dots =
    Dots
  | Nest of sequence
  | When of dots * sequence

and dots_bef_aft =
    NoDots
  | AddingBetweenDots of term * int (*index of let var*)
  | DroppingBetweenDots of term * int (*index of let var*)

