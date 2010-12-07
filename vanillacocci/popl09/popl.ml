type cocci_predicate = Lib_engine.predicate * Ast_cocci.meta_name Ast_ctl.modif
type formula =
    (cocci_predicate,Ast_cocci.meta_name, Wrapper_ctl.info) Ast_ctl.generic_ctl

let poplz (name,_,ast) =
  match ast with
    [ast] ->
      let ast = Asttopopl.top ast in
      let qt = Insert_quantifiers.insert_quantifiers ast in
      [Popltoctl.toctl qt]
  | _ -> failwith "only one rule allowed"

let popl r =
  match r with
    Ast_cocci.CocciRule(a,b,c,_,Ast_cocci.Normal) -> poplz (a,b,c)
  | _ -> []
