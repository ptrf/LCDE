open Ast_c
open Common
open Pycaml
open Pycocci_aux
module StringMap = Map.Make (String)

exception Pycocciexception

let python_support = true

(* ------------------------------------------------------------------- *)
(* The following definitions are from
http://patches.ubuntu.com/by-release/extracted/debian/c/coccinelle/0.1.5dbs-2/01-system-pycaml
as well as _pycocci_setargs *)

let _pycocci_none () =
  let builtins = pyeval_getbuiltins () in
  pyobject_getitem (builtins, pystring_fromstring "None")

let _pycocci_true () =
  let builtins = pyeval_getbuiltins () in
  pyobject_getitem (builtins, pystring_fromstring "True")

let _pycocci_false () =
  let builtins = pyeval_getbuiltins () in
  pyobject_getitem (builtins, pystring_fromstring "False")

let _pycocci_tuple6 (a,b,c,d,e,f) =
  pytuple_fromarray ([|a; b; c; d; e; f|])

(* ------------------------------------------------------------------- *)

let check_return_value v =
  if v =*= (pynull ()) then
	  (pyerr_print ();
	  raise Pycocciexception)
  else ()
let check_int_return_value v =
  if v =|= -1 then
	  (pyerr_print ();
	  raise Pycocciexception)
  else ()

let initialised = ref false

let coccinelle_module = ref (_pycocci_none ())
let cocci_file_name = ref ""

(* dealing with python modules loaded *)
let module_map = ref (StringMap.add "__main__" (_pycocci_none ()) StringMap.empty)

let get_module module_name =
  StringMap.find module_name (!module_map)

let is_module_loaded module_name =
  try
    let _ = get_module module_name in
    true
  with Not_found -> false

let load_module module_name =
  if not (is_module_loaded module_name) then
    let m = pyimport_importmodule module_name in
    check_return_value m;
    (module_map := (StringMap.add module_name m (!module_map));
    m)
  else get_module module_name
(* end python module handling part *)

(* python interaction *)
let split_fqn fqn =
  let last_period = String.rindex fqn '.' in
  let module_name = String.sub fqn 0 last_period in
  let class_name = String.sub fqn (last_period + 1) (String.length fqn - last_period - 1) in
  (module_name, class_name)

let pycocci_get_class_type fqn =
  let (module_name, class_name) = split_fqn fqn in
  let m = get_module module_name in
  let attr = pyobject_getattrstring(m, class_name) in
  check_return_value attr;
  attr

let pycocci_instantiate_class fqn args =
  let class_type = pycocci_get_class_type fqn in
  let obj =
    pyeval_callobjectwithkeywords(class_type, args, pynull()) in
  check_return_value obj;
  obj

(* end python interaction *)

let inc_match = ref true

let include_match v =
  let truth = pyobject_istrue (pytuple_getitem (v, 1)) in
  check_int_return_value truth;
  inc_match := truth != 0;
  _pycocci_none ()

let build_method (mname, camlfunc, args) pymodule classx classdict =
  let cmx = pymethod_new(pywrap_closure camlfunc, args, classx) in
  let v = pydict_setitemstring(classdict, mname, cmx) in
  check_int_return_value v;
  ()

let build_class cname parent methods pymodule =
  let cd = pydict_new() in
  check_return_value cd;
  let cx = pyclass_new(pytuple_fromsingle (pycocci_get_class_type parent), cd,
		       pystring_fromstring cname) in
  check_return_value cx;
  List.iter (function meth -> build_method meth pymodule cx cd) methods;
  let v = pydict_setitemstring(pymodule_getdict pymodule, cname, cx) in
  check_int_return_value v;
  (cd, cx)

let the_environment = ref []

let has_environment_binding name =
  let a = pytuple_toarray name in
  let (rule, name) = (Array.get a 1, Array.get a 2) in
  let orule = pystring_asstring rule in
  let oname = pystring_asstring name in
  let e = List.exists (function (x,y) -> orule =*= x && oname =$= y)
      !the_environment in
  if e then _pycocci_true () else _pycocci_false ()

let pyoutputinstance = ref (_pycocci_none ())
let pyoutputdict = ref (_pycocci_none ())

let get_cocci_file args =
  pystring_fromstring (!cocci_file_name)

(* initialisation routines *)
let _pycocci_setargs argv0 =
  let argv =
    pysequence_list (pytuple_fromsingle (pystring_fromstring argv0)) in
  let sys_mod = load_module "sys" in
  pyobject_setattrstring (sys_mod, "argv", argv)

let pycocci_init () =
  (* initialize *)
  if not !initialised then (
  initialised := true;
  Unix.putenv "PYTHONPATH"
      (Printf.sprintf "%s/coccinelle" (Unix.getenv "HOME"));
  let _ = if not (py_isinitialized () != 0) then
  	(if !Flag.show_misc then Common.pr2 "Initializing python\n%!";
	py_initialize()) in

  (* set argv *)
  let argv0 = Printf.sprintf "%s%sspatch" (Sys.getcwd ()) (match Sys.os_type with "Win32" -> "\\" | _ -> "/") in
  let _ = _pycocci_setargs argv0 in

  coccinelle_module := (pymodule_new "coccinelle");
  module_map := StringMap.add "coccinelle" !coccinelle_module !module_map;
  let _ = load_module "coccilib.elems" in
  let _ = load_module "coccilib.output" in

  let module_dictionary = pyimport_getmoduledict() in
  coccinelle_module := pymodule_new "coccinelle";
  let mx = !coccinelle_module in
  let (cd, cx) = build_class "Cocci" (!Flag.pyoutput)
      [("include_match", include_match, (pynull()));
	("has_env_binding", has_environment_binding, (pynull()))] mx in
  pyoutputinstance := cx;
  pyoutputdict := cd;
  let v1 = pydict_setitemstring(module_dictionary, "coccinelle", mx) in
  check_int_return_value v1;
  let mypystring = pystring_fromstring !cocci_file_name in
  let v2 = pydict_setitemstring(cd, "cocci_file", mypystring) in
  check_int_return_value v2;
  ()) else
  ()

(*let _ = pycocci_init ()*)
(* end initialisation routines *)

let added_variables = ref []

let build_classes env =
  let _ = pycocci_init () in
  inc_match := true;
  the_environment := env;
  let mx = !coccinelle_module in
  let dict = pymodule_getdict mx in
  List.iter
    (function
	"include_match" | "has_env_binding" -> ()
      | name ->
	  let v = pydict_delitemstring(dict,name) in
	  check_int_return_value v)
    !added_variables;
  added_variables := [];
  ()

let build_variable name value =
  let mx = !coccinelle_module in
  added_variables := name :: !added_variables;
  check_int_return_value
    (pydict_setitemstring(pymodule_getdict mx, name, value))

let get_variable name =
  let mx = !coccinelle_module in
  pystring_asstring
    (pyobject_str(pydict_getitemstring(pymodule_getdict mx, name)))

let contains_binding e (_,(r,m),_) =
  try
    let _ = List.find (function ((re, rm), _) -> r =*= re && m =$= rm) e in
    true
  with Not_found -> false

let construct_variables mv e =
  let find_binding (r,m) =
    try
      let elem = List.find (function ((re,rm),_) -> r =*= re && m =$= rm) e in
      Some elem
    with Not_found -> None
  in

  let instantiate_Expression(x) =
    let str = pystring_fromstring (Pycocci_aux.exprrep x) in
    pycocci_instantiate_class "coccilib.elems.Expression"
      (pytuple_fromsingle (str))
  in

  let instantiate_Identifier(x) =
    let str = pystring_fromstring x in
    pycocci_instantiate_class "coccilib.elems.Identifier"
      (pytuple_fromsingle (str))
  in

  List.iter (function (py,(r,m),_) ->
    match find_binding (r,m) with
      None -> ()
    | Some (_, Ast_c.MetaExprVal (expr,_)) ->
       let expr_repr = instantiate_Expression(expr) in
       let _ = build_variable py expr_repr in
       ()
    | Some (_, Ast_c.MetaIdVal (id,_)) ->
       let id_repr = instantiate_Identifier(id) in
       let _ = build_variable py id_repr in
       ()
    | Some (_, Ast_c.MetaPosValList l) ->
       let locs =
	 List.map
	   (function (fname,current_element,(line,col),(line_end,col_end)) ->
		pycocci_instantiate_class "coccilib.elems.Location"
	       (_pycocci_tuple6
		(pystring_fromstring fname,pystring_fromstring current_element,
		pystring_fromstring (Printf.sprintf "%d" line),
		pystring_fromstring (Printf.sprintf "%d" col),
		pystring_fromstring (Printf.sprintf "%d" line_end),
		pystring_fromstring (Printf.sprintf "%d" col_end)))) l in
       let pylocs = pytuple_fromarray (Array.of_list locs) in
       let _ = build_variable py pylocs in
       ()
    | Some (_,binding) ->
       let _ =
	 build_variable py
	   (pystring_fromstring (Pycocci_aux.stringrep binding)) in
       ()
    ) mv;

  ()

let construct_script_variables mv =
  List.iter
    (function (_,py) ->
      let vl =
	let str = pystring_fromstring "initial value" in
	pycocci_instantiate_class "coccilib.elems.Identifier"
	  (pytuple_fromsingle (str)) in
      let _ = build_variable py vl in
      ())
    mv

let retrieve_script_variables mv =
  List.map (function (_,py) -> get_variable py) mv

let set_coccifile cocci_file =
	cocci_file_name := cocci_file;
	()

let pyrun_simplestring s =
  let res = Pycaml.pyrun_simplestring s in
  check_int_return_value res;
  res

let py_isinitialized () =
  Pycaml.py_isinitialized ()


let py_finalize () =
  Pycaml.py_finalize ()
