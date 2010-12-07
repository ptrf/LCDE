open Common

module CCI = Ctlcocci_integration
module TAC = Type_annoter_c

module Ast_to_flow = Control_flow_c_build

(*****************************************************************************)
(* This file is a kind of driver. It gathers all the important functions
 * from coccinelle in one place. The different entities in coccinelle are:
 *  - files
 *  - astc
 *  - astcocci
 *  - flow (contain nodes)
 *  - ctl  (contain rule_elems)
 * This file contains functions to transform one in another.
 *)
(*****************************************************************************)

(* --------------------------------------------------------------------- *)
(* C related *)
(* --------------------------------------------------------------------- *)
let cprogram_of_file file =
  let (program2, _stat) = Parse_c.parse_c_and_cpp file in
  program2

let cprogram_of_file_cached file =
  let (program2, _stat) = Parse_c.parse_cache file in
  if !Flag_cocci.ifdef_to_if
  then
    program2 +> Parse_c.with_program2 (fun asts ->
      Cpp_ast_c.cpp_ifdef_statementize asts
    )
  else program2

let cfile_of_program program2_with_ppmethod outf =
  Unparse_c.pp_program program2_with_ppmethod outf

(* for memoization, contains only one entry, the one for the SP *)
let _hparse = Hashtbl.create 101
let _hctl = Hashtbl.create 101

(* --------------------------------------------------------------------- *)
(* Cocci related *)
(* --------------------------------------------------------------------- *)
let sp_of_file2 file iso   =
  Common.memoized _hparse (file, iso) (fun () ->
    let (_,xs,_,_,_,_,_) as res = Parse_cocci.process file iso false in
    (match Prepare_ocamlcocci.prepare file xs with
      None -> ()
    | Some ocaml_script_file ->
        (* compile file *)
	Prepare_ocamlcocci.load_file ocaml_script_file;
	if not !Common.save_tmp_files
	then Prepare_ocamlcocci.clean_file ocaml_script_file);
    res)
let sp_of_file file iso    =
  Common.profile_code "parse cocci" (fun () -> sp_of_file2 file iso)


(* --------------------------------------------------------------------- *)
(* Flow related *)
(* --------------------------------------------------------------------- *)
let print_flow flow =
  Ograph_extended.print_ograph_mutable flow "/tmp/test.dot" true


let ast_to_flow_with_error_messages2 x =
  let flowopt =
    try Ast_to_flow.ast_to_control_flow x
    with Ast_to_flow.Error x ->
      Ast_to_flow.report_error x;
      None
  in
  flowopt +> do_option (fun flow ->
    (* This time even if there is a deadcode, we still have a
     * flow graph, so I can try the transformation and hope the
     * deadcode will not bother us.
     *)
    try Ast_to_flow.deadcode_detection flow
    with Ast_to_flow.Error (Ast_to_flow.DeadCode x) ->
      Ast_to_flow.report_error (Ast_to_flow.DeadCode x);
  );
  flowopt
let ast_to_flow_with_error_messages a =
  Common.profile_code "flow" (fun () -> ast_to_flow_with_error_messages2 a)


(* --------------------------------------------------------------------- *)
(* Ctl related *)
(* --------------------------------------------------------------------- *)

let ctls_of_ast2 ast (ua,fua,fuas) pos =
  List.map2
    (function ast -> function (ua,(fua,(fuas,pos))) ->
      List.combine
	(if !Flag_cocci.popl
	then Popl.popl ast
	else Asttoctl2.asttoctl ast (ua,fua,fuas) pos)
	(Asttomember.asttomember ast ua))
    ast (List.combine ua (List.combine fua (List.combine fuas pos)))

let ctls_of_ast ast ua =
  Common.profile_code "asttoctl2" (fun () -> ctls_of_ast2 ast ua)

(*****************************************************************************)
(* Some  debugging functions *)
(*****************************************************************************)

(* the inputs *)

let show_or_not_cfile2 cfile =
  if !Flag_cocci.show_c then begin
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    pr2 ("processing C file: " ^ cfile);
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    Common.command2 ("cat " ^ cfile);
  end
let show_or_not_cfile a =
  Common.profile_code "show_xxx" (fun () -> show_or_not_cfile2 a)

let show_or_not_cfiles cfiles = List.iter show_or_not_cfile cfiles


let show_or_not_cocci2 coccifile isofile =
  if !Flag_cocci.show_cocci then begin
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    pr2 ("processing semantic patch file: " ^ coccifile);
    isofile +> (fun s -> pr2 ("with isos from: " ^ s));
    Common.pr2_xxxxxxxxxxxxxxxxx ();
    Common.command2 ("cat " ^ coccifile);
    pr2 "";
  end
let show_or_not_cocci a b =
  Common.profile_code "show_xxx" (fun () -> show_or_not_cocci2 a b)

(* ---------------------------------------------------------------------- *)
(* the output *)

let fix_sgrep_diffs l =
  let l =
    List.filter (function s -> (s =~ "^\\+\\+\\+") || not (s =~ "^\\+")) l in
  let l = List.rev l in
  (* adjust second number for + code *)
  let rec loop1 n = function
      [] -> []
    | s::ss ->
	if s =~ "^-" && not(s =~ "^---")
	then s :: loop1 (n+1) ss
	else if s =~ "^@@"
	then
	  (match Str.split (Str.regexp " ") s with
	    bef::min::pl::aft ->
	      let (n1,n2) =
		match Str.split (Str.regexp ",") pl with
		  [n1;n2] -> (n1,n2)
		| [n1] -> (n1,"1")
		| _ -> failwith "bad + line information" in
	      let n2 = int_of_string n2 in
	      (Printf.sprintf "%s %s %s,%d %s" bef min n1 (n2-n)
		 (String.concat " " aft))
	      :: loop1 0 ss
	  | _ -> failwith "bad @@ information")
	else s :: loop1 n ss in
  let rec loop2 n = function
      [] -> []
    | s::ss ->
	if s =~ "^---"
	then s :: loop2 0 ss
	else if s =~ "^@@"
	then
	  (match Str.split (Str.regexp " ") s with
	    bef::min::pl::aft ->
	      let (m2,n1,n2) =
		match (Str.split (Str.regexp ",") min,
		       Str.split (Str.regexp ",") pl) with
		  ([_;m2],[n1;n2]) -> (m2,n1,n2)
		| ([_],[n1;n2]) -> ("1",n1,n2)
		| ([_;m2],[n1]) -> (m2,n1,"1")
		| ([_],[n1]) -> ("1",n1,"1")
		| _ -> failwith "bad -/+ line information" in
	      let n1 =
		int_of_string (String.sub n1 1 ((String.length n1)-1)) in
	      let m2 = int_of_string m2 in
	      let n2 = int_of_string n2 in
	      (Printf.sprintf "%s %s +%d,%d %s" bef min (n1-n) n2
		 (String.concat " " aft))
	      :: loop2 (n+(m2-n2)) ss
	  | _ -> failwith "bad @@ information")
	else s :: loop2 n ss in
  loop2 0 (List.rev (loop1 0 l))

let normalize_path file =
  let fullpath =
    if String.get file 0 = '/' then file else (Sys.getcwd()) ^ "/" ^ file in
  let elements = Str.split_delim (Str.regexp "/") fullpath in
  let rec loop prev = function
      [] -> String.concat "/" (List.rev prev)
    | "." :: rest -> loop prev rest
    | ".." :: rest ->
	(match prev with
	  x::xs -> loop xs rest
	| _ -> failwith "bad path")
    | x::rest -> loop (x::prev) rest in
  loop [] elements

let show_or_not_diff2 cfile outfile =
  if !Flag_cocci.show_diff then begin
    match Common.fst(Compare_c.compare_to_original cfile outfile) with
      Compare_c.Correct -> () (* diff only in spacing, etc *)
    | _ ->
        (* may need --strip-trailing-cr under windows *)
	pr2 "diff = ";

	let line =
	  match !Flag_parsing_c.diff_lines with
	  | None ->   "diff -u -p " ^ cfile ^ " " ^ outfile
	  | Some n -> "diff -U "^n^" -p "^cfile^" "^outfile in
	let xs =
	  let res = Common.cmd_to_list line in
	  match (!Flag.patch,res) with
	(* create something that looks like the output of patch *)
	    (Some prefix,minus_file::plus_file::rest) ->
	      let prefix =
		let lp = String.length prefix in
		if String.get prefix (lp-1) = '/'
		then String.sub prefix 0 (lp-1)
		else prefix in
	      let drop_prefix file =
		let file = normalize_path file in
		if Str.string_match (Str.regexp prefix) file 0
		then
		  let lp = String.length prefix in
		  let lf = String.length file in
		  if lp < lf
		  then String.sub file lp (lf - lp)
		  else
		    failwith
		      (Printf.sprintf "prefix %s doesn't match file %s"
			 prefix file)
		else
		  failwith
		    (Printf.sprintf "prefix %s doesn't match file %s"
		       prefix file) in
	      let diff_line =
		match List.rev(Str.split (Str.regexp " ") line) with
		  new_file::old_file::cmdrev ->
		    let old_base_file = drop_prefix old_file in
		    if !Flag.sgrep_mode2
		    then
		      String.concat " "
			(List.rev
			   (("/tmp/nothing"^old_base_file)
			    :: old_file :: cmdrev))
		    else
		      String.concat " "
			(List.rev
			   (("b"^old_base_file)::("a"^old_base_file)::cmdrev))
		| _ -> failwith "bad command" in
	      let (minus_line,plus_line) =
		match (Str.split (Str.regexp "[ \t]") minus_file,
		       Str.split (Str.regexp "[ \t]") plus_file) with
		  ("---"::old_file::old_rest,"+++"::new_file::new_rest) ->
		    let old_base_file = drop_prefix old_file in
		    if !Flag.sgrep_mode2
		    then (minus_file,"+++ /tmp/nothing"^old_base_file)
		    else
		      (String.concat " "
			 ("---"::("a"^old_base_file)::old_rest),
		       String.concat " "
			 ("+++"::("b"^old_base_file)::new_rest))
		  | (l1,l2) ->
		      failwith
			(Printf.sprintf "bad diff header lines: %s %s"
			   (String.concat ":" l1) (String.concat ":" l2)) in
	      diff_line::minus_line::plus_line::rest
	  | _ -> res in
	let xs = if !Flag.sgrep_mode2 then fix_sgrep_diffs xs else xs in
	xs +> List.iter pr
  end
let show_or_not_diff a b =
  Common.profile_code "show_xxx" (fun () -> show_or_not_diff2 a b)


(* the derived input *)

let show_or_not_ctl_tex2 astcocci ctls =
  if !Flag_cocci.show_ctl_tex then begin
    Ctltotex.totex ("/tmp/__cocci_ctl.tex") astcocci ctls;
    Common.command2 ("cd /tmp; latex __cocci_ctl.tex; " ^
		     "dvips __cocci_ctl.dvi -o __cocci_ctl.ps;" ^
		     "gv __cocci_ctl.ps &");
  end
let show_or_not_ctl_tex a b  =
  Common.profile_code "show_xxx" (fun () -> show_or_not_ctl_tex2 a b)


let show_or_not_rule_name ast rulenb =
  if !Flag_cocci.show_ctl_text or !Flag.show_trying or
    !Flag.show_transinfo or !Flag_cocci.show_binding_in_out
  then
    begin
      let name =
	match ast with
	  Ast_cocci.CocciRule (nm, (deps, drops, exists), x, _, _) -> nm
	| _ -> i_to_s rulenb in
      Common.pr_xxxxxxxxxxxxxxxxx ();
      pr (name ^ " = ");
      Common.pr_xxxxxxxxxxxxxxxxx ()
    end

let show_or_not_scr_rule_name rulenb =
  if !Flag_cocci.show_ctl_text or !Flag.show_trying or
    !Flag.show_transinfo or !Flag_cocci.show_binding_in_out
  then
    begin
      let name = i_to_s rulenb in
      Common.pr_xxxxxxxxxxxxxxxxx ();
      pr ("script rule " ^ name ^ " = ");
      Common.pr_xxxxxxxxxxxxxxxxx ()
    end

let show_or_not_ctl_text2 ctl ast rulenb =
  if !Flag_cocci.show_ctl_text then begin

    adjust_pp_with_indent (fun () ->
      Format.force_newline();
      Pretty_print_cocci.print_plus_flag := true;
      Pretty_print_cocci.print_minus_flag := true;
      Pretty_print_cocci.unparse ast;
      );

    pr "CTL = ";
    let (ctl,_) = ctl in
    adjust_pp_with_indent (fun () ->
      Format.force_newline();
      Pretty_print_engine.pp_ctlcocci
        !Flag_cocci.show_mcodekind_in_ctl !Flag_cocci.inline_let_ctl ctl;
      );
    pr "";
  end
let show_or_not_ctl_text a b c =
      Common.profile_code "show_xxx" (fun () -> show_or_not_ctl_text2 a b c)



(* running information *)
let get_celem celem : string =
  match celem with
      Ast_c.Definition ({Ast_c.f_name = namefuncs;},_) ->
        Ast_c.str_of_name namefuncs
    | Ast_c.Declaration
	(Ast_c.DeclList ([{Ast_c.v_namei = Some (name, _);}, _], _)) ->
        Ast_c.str_of_name name
    | _ -> ""

let show_or_not_celem2 prelude celem =
  let (tag,trying) =
  (match celem with
  | Ast_c.Definition ({Ast_c.f_name = namefuncs},_) ->
      let funcs = Ast_c.str_of_name namefuncs in
      Flag.current_element := funcs;
      (" function: ",funcs)
  | Ast_c.Declaration
      (Ast_c.DeclList ([{Ast_c.v_namei = Some (name,_)}, _], _)) ->
      let s = Ast_c.str_of_name name in
      Flag.current_element := s;
      (" variable ",s);
  | _ ->
      Flag.current_element := "something_else";
      (" ","something else");
  ) in
  if !Flag.show_trying then pr2 (prelude ^ tag ^ trying)

let show_or_not_celem a b  =
  Common.profile_code "show_xxx" (fun () -> show_or_not_celem2 a b)


let show_or_not_trans_info2 trans_info =
  (* drop witness tree indices for printing *)
  let trans_info =
    List.map (function (index,trans_info) -> trans_info) trans_info in
  if !Flag.show_transinfo then begin
    if null trans_info then pr2 "transformation info is empty"
    else begin
      pr2 "transformation info returned:";
      let trans_info =
        List.sort (function (i1,_,_) -> function (i2,_,_) -> compare i1 i2)
          trans_info
      in
      indent_do (fun () ->
        trans_info +> List.iter (fun (i, subst, re) ->
          pr2 ("transform state: " ^ (Common.i_to_s i));
          indent_do (fun () ->
            adjust_pp_with_indent_and_header "with rule_elem: " (fun () ->
              Pretty_print_cocci.print_plus_flag := true;
              Pretty_print_cocci.print_minus_flag := true;
              Pretty_print_cocci.rule_elem "" re;
            );
            adjust_pp_with_indent_and_header "with binding: " (fun () ->
              Pretty_print_engine.pp_binding subst;
            );
          )
        );
      )
    end
  end
let show_or_not_trans_info a  =
  Common.profile_code "show_xxx" (fun () -> show_or_not_trans_info2 a)



let show_or_not_binding2 s binding =
  if !Flag_cocci.show_binding_in_out then begin
    adjust_pp_with_indent_and_header ("binding " ^ s ^ " = ") (fun () ->
      Pretty_print_engine.pp_binding binding
    )
  end
let show_or_not_binding a b  =
  Common.profile_code "show_xxx" (fun () -> show_or_not_binding2 a b)



(*****************************************************************************)
(* Some  helper functions *)
(*****************************************************************************)

let worth_trying cfiles tokens =
  (* drop the following line for a list of list by rules.  since we don't
     allow multiple minirules, all the tokens within a rule should be in
     a single CFG entity *)
  match (!Flag_cocci.windows,tokens) with
    (true,_) | (_,None) -> true
  | (_,Some tokens) ->
   (* could also modify the code in get_constants.ml *)
      let tokens = tokens +> List.map (fun s ->
	match () with
	| _ when s =~ "^[A-Za-z_][A-Za-z_0-9]*$" ->
            "\\b" ^ s ^ "\\b"

	| _ when s =~ "^[A-Za-z_]" ->
            "\\b" ^ s

	| _ when s =~ ".*[A-Za-z_]$" ->
            s ^ "\\b"
	| _ -> s

      ) in
      let com = sprintf "egrep -q '(%s)' %s" (join "|" tokens) (join " " cfiles)
      in
      (match Sys.command com with
      | 0 (* success *) -> true
      | _ (* failure *) ->
	  (if !Flag.show_misc
	  then Printf.printf "grep failed: %s\n" com);
	  false (* no match, so not worth trying *))

let check_macro_in_sp_and_adjust = function
    None -> ()
  | Some tokens ->
      tokens +> List.iter (fun s ->
	if Hashtbl.mem !Parse_c._defs s
	then begin
	  if !Flag_cocci.verbose_cocci then begin
            pr2 "warning: macro in semantic patch was in macro definitions";
            pr2 ("disabling macro expansion for " ^ s);
	  end;
	  Hashtbl.remove !Parse_c._defs s
	end)


let contain_loop gopt =
  match gopt with
  | Some g ->
      g#nodes#tolist +> List.exists (fun (xi, node) ->
        Control_flow_c.extract_is_loop node
      )
  | None -> true (* means nothing, if no g then will not model check *)



let sp_contain_typed_metavar_z toplevel_list_list =
  let bind x y = x or y in
  let option_default = false in
  let mcode _ _ = option_default in
  let donothing r k e = k e in

  let expression r k e =
    match Ast_cocci.unwrap e with
    | Ast_cocci.MetaExpr (_,_,_,Some t,_,_) -> true
    | Ast_cocci.MetaExpr (_,_,_,_,Ast_cocci.LocalID,_) -> true
    | _ -> k e
  in

  let combiner =
    Visitor_ast.combiner bind option_default
      mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode mcode
      donothing donothing donothing donothing donothing
      donothing expression donothing donothing donothing donothing donothing
      donothing donothing donothing donothing donothing
  in
  toplevel_list_list +>
    List.exists
    (function (nm,_,rule) ->
      (List.exists combiner.Visitor_ast.combiner_top_level rule))

let sp_contain_typed_metavar rules =
  sp_contain_typed_metavar_z
    (List.map
       (function x ->
	 match x with
	   Ast_cocci.CocciRule (a,b,c,d,_) -> (a,b,c)
	 | _ -> failwith "error in filter")
    (List.filter
       (function x ->
	 match x with
	   Ast_cocci.CocciRule (a,b,c,d,Ast_cocci.Normal) -> true
	 | _ -> false)
       rules))



(* finding among the #include the one that we need to parse
 * because they may contain useful type definition or because
 * we may have to modify them
 *
 * For the moment we base in part our heuristic on the name of the file, e.g.
 * serio.c is related we think to #include <linux/serio.h>
 *)
let rec search_include_path searchlist relpath =
  match searchlist with
      []       -> Some relpath
    | hd::tail ->
	let file = Filename.concat hd relpath in
	if Sys.file_exists file then
	  Some file
	else
	  search_include_path tail relpath

let interpret_include_path relpath =
  let searchlist =
    match !Flag_cocci.include_path with
	[] -> ["include"]
      | x -> List.rev x
  in
    search_include_path searchlist relpath

let (includes_to_parse:
       (Common.filename * Parse_c.program2) list ->
	 Flag_cocci.include_options -> 'a) = fun xs choose_includes ->
  match choose_includes with
    Flag_cocci.I_UNSPECIFIED -> failwith "not possible"
  | Flag_cocci.I_NO_INCLUDES -> []
  | x ->
      let all_includes =
	List.mem x
	  [Flag_cocci.I_ALL_INCLUDES; Flag_cocci.I_REALLY_ALL_INCLUDES] in
      xs +> List.map (fun (file, cs) ->
	let dir = Common.dirname file in

	cs +> Common.map_filter (fun (c,_info_item) ->
	  match c with
	  | Ast_c.CppTop
	      (Ast_c.Include
		 {Ast_c.i_include = ((x,ii)); i_rel_pos = info_h_pos;})  ->
	    (match x with
            | Ast_c.Local xs ->
		let relpath = Common.join "/" xs in
		let f = Filename.concat dir (relpath) in
		if (Sys.file_exists f) then
		  Some f
		else
		  if !Flag_cocci.relax_include_path
	      (* for our tests, all the files are flat in the current dir *)
		  then
		    let attempt2 = Filename.concat dir (Common.last xs) in
		      if not (Sys.file_exists attempt2) && all_includes
		      then
			interpret_include_path relpath
		      else Some attempt2
		  else
		    if all_includes then interpret_include_path relpath
		    else None

            | Ast_c.NonLocal xs ->
		let relpath = Common.join "/" xs in
		if all_includes ||
	        Common.fileprefix (Common.last xs) =$= Common.fileprefix file
		then
		  interpret_include_path relpath
		else None
            | Ast_c.Weird _ -> None
		  )
	  | _ -> None))
	+> List.concat
	+> (fun x -> (List.rev (Common.uniq (List.rev x)))) (*uniq keeps last*)

let rec interpret_dependencies local global = function
    Ast_cocci.Dep s      -> List.mem s local
  | Ast_cocci.AntiDep s  ->
      (if !Flag_ctl.steps != None
      then failwith "steps and ! dependency incompatible");
      not (List.mem s local)
  | Ast_cocci.EverDep s  -> List.mem s global
  | Ast_cocci.NeverDep s ->
      (if !Flag_ctl.steps != None
      then failwith "steps and ! dependency incompatible");
      not (List.mem s global)
  | Ast_cocci.AndDep(s1,s2) ->
      (interpret_dependencies local global s1) &&
      (interpret_dependencies local global s2)
  | Ast_cocci.OrDep(s1,s2)  ->
      (interpret_dependencies local global s1) or
      (interpret_dependencies local global s2)
  | Ast_cocci.NoDep -> true
  | Ast_cocci.FailDep -> false

let rec print_dependencies str local global dep =
  if !Flag_cocci.show_dependencies
  then
    begin
      pr2 str;
      let seen = ref [] in
      let rec loop = function
	  Ast_cocci.Dep s | Ast_cocci.AntiDep s ->
	      if not (List.mem s !seen)
	      then
		begin
		  if List.mem s local
		  then pr2 (s^" satisfied")
		  else pr2 (s^" not satisfied");
		  seen := s :: !seen
		end
	| Ast_cocci.EverDep s | Ast_cocci.NeverDep s ->
	      if not (List.mem s !seen)
	      then
		begin
		  if List.mem s global
		  then pr2 (s^" satisfied")
		  else pr2 (s^" not satisfied");
		  seen := s :: !seen
		end
	| Ast_cocci.AndDep(s1,s2) ->
	    loop s1;
	    loop s2
	| Ast_cocci.OrDep(s1,s2)  ->
	    loop s1;
	    loop s2
	| Ast_cocci.NoDep -> ()
	| Ast_cocci.FailDep -> pr2 "False not satisfied" in
      loop dep
    end

(* --------------------------------------------------------------------- *)
(* #include relative position in the file *)
(* --------------------------------------------------------------------- *)

(* compute the set of new prefixes
 * on
 *  "a/b/x"; (* in fact it is now a list of string so  ["a";"b";"x"] *)
 *  "a/b/c/x";
 *  "a/x";
 *  "b/x";
 * it would give for the first element
 *   ""; "a"; "a/b"; "a/b/x"
 * for the second
 *   "a/b/c/x"
 *
 * update: if the include is inside a ifdef a put nothing. cf -test incl.
 * this is because we dont want code added inside ifdef.
 *)

let compute_new_prefixes xs =
  xs +> Common.map_withenv (fun already xs ->
    let subdirs_prefixes = Common.inits xs in
    let new_first = subdirs_prefixes +> List.filter (fun x ->
      not (List.mem x already)
    )
    in
    new_first,
    new_first @ already
  ) []
  +> fst


(* does via side effect on the ref in the Include in Ast_c *)
let rec update_include_rel_pos cs =
  let only_include = cs +> Common.map_filter (fun c ->
    match c with
    | Ast_c.CppTop (Ast_c.Include {Ast_c.i_include = ((x,_));
                     i_rel_pos = aref;
                     i_is_in_ifdef = inifdef}) ->
        (match x with
        | Ast_c.Weird _ -> None
        | _ ->
            if inifdef
            then None
            else Some (x, aref)
        )
    | _ -> None
  )
  in
  let (locals, nonlocals) =
    only_include +> Common.partition_either (fun (c, aref)  ->
      match c with
      | Ast_c.Local x -> Left (x, aref)
      | Ast_c.NonLocal x -> Right (x, aref)
      | Ast_c.Weird x -> raise Impossible
    ) in

  update_rel_pos_bis locals;
  update_rel_pos_bis nonlocals;
  cs
and update_rel_pos_bis xs =
  let xs' = List.map fst xs in
  let the_first = compute_new_prefixes xs' in
  let the_last  = List.rev (compute_new_prefixes (List.rev xs')) in
  let merged = Common.zip xs (Common.zip the_first the_last) in
  merged +> List.iter (fun ((x, aref), (the_first, the_last)) ->
    aref := Some
      {
        Ast_c.first_of = the_first;
        Ast_c.last_of = the_last;
      }
  )


(*****************************************************************************)
(* All the information needed around the C elements and Cocci rules *)
(*****************************************************************************)

type toplevel_c_info = {
  ast_c: Ast_c.toplevel; (* contain refs so can be modified *)
  tokens_c: Parser_c.token list;
  fullstring: string;

  flow: Control_flow_c.cflow option; (* it's the "fixed" flow *)
  contain_loop: bool;

  env_typing_before: TAC.environment;
  env_typing_after:  TAC.environment;

  was_modified: bool ref;

  (* id: int *)
}

type rule_info = {
  rulename: string;
  dependencies: Ast_cocci.dependency;
  used_after: Ast_cocci.meta_name list;
  ruleid: int;
  was_matched: bool ref;
} 

type toplevel_cocci_info_script_rule = {
  scr_ast_rule:
      string *
      (Ast_cocci.script_meta_name * Ast_cocci.meta_name *
	 Ast_cocci.metavar) list *
      Ast_cocci.meta_name list (*fresh vars*) *
      string;
  language: string;
  script_code: string;
  scr_rule_info: rule_info;
}

type toplevel_cocci_info_cocci_rule = {
  ctl: Lib_engine.ctlcocci * (CCI.pred list list);
  metavars: Ast_cocci.metavar list;
  ast_rule: Ast_cocci.rule;
  isexp: bool; (* true if + code is an exp, only for Flag.make_hrule *)

  (* There are also some hardcoded rule names in parse_cocci.ml:
   *  let reserved_names = ["all";"optional_storage";"optional_qualifier"]
   *)
  dropped_isos: string list;
  free_vars:  Ast_cocci.meta_name list;
  negated_pos_vars:  Ast_cocci.meta_name list;
  positions: Ast_cocci.meta_name list;

  ruletype: Ast_cocci.ruletype;

  rule_info: rule_info;
}

type toplevel_cocci_info =
    ScriptRuleCocciInfo of toplevel_cocci_info_script_rule
  | InitialScriptRuleCocciInfo of toplevel_cocci_info_script_rule
  | FinalScriptRuleCocciInfo of toplevel_cocci_info_script_rule
  | CocciRuleCocciInfo of toplevel_cocci_info_cocci_rule

type cocci_info = toplevel_cocci_info list * string list option (* tokens *)

type kind_file = Header | Source
type file_info = {
  fname : string;
  full_fname : string;
  was_modified_once: bool ref;
  asts: toplevel_c_info list;
  fpath : string;
  fkind : kind_file;
}

let g_contain_typedmetavar = ref false


let last_env_toplevel_c_info xs =
  (Common.last xs).env_typing_after

let concat_headers_and_c (ccs: file_info list)
    : (toplevel_c_info * string) list =
  (List.concat (ccs +> List.map (fun x ->
				   x.asts +> List.map (fun x' ->
							 (x', x.fname)))))

let for_unparser xs =
  xs +> List.map (fun x ->
    (x.ast_c, (x.fullstring, x.tokens_c)), Unparse_c.PPviastr
  )

let gen_pdf_graph () =
  (Ctl_engine.get_graph_files ()) +> List.iter (fun outfile ->
  Printf.printf "Generation of %s%!" outfile;
  let filename_stack = Ctl_engine.get_graph_comp_files outfile in
  List.iter (fun filename ->
    ignore (Unix.system ("dot " ^ filename ^ " -Tpdf  -o " ^ filename ^ ".pdf;"))
	    ) filename_stack;
  let (head,tail) = (List.hd filename_stack, List.tl filename_stack) in
    ignore(Unix.system ("cp " ^ head ^ ".pdf " ^ outfile ^ ".pdf;"));
    tail +> List.iter (fun filename ->
      ignore(Unix.system ("mv " ^ outfile ^ ".pdf /tmp/tmp.pdf;"));
      ignore(Unix.system ("pdftk " ^ filename ^ ".pdf /tmp/tmp.pdf cat output " ^ outfile ^ ".pdf"));
	      );
    ignore(Unix.system ("rm /tmp/tmp.pdf;"));
    List.iter (fun filename ->
	ignore (Unix.system ("rm " ^ filename ^ " " ^ filename ^ ".pdf;"))
	    ) filename_stack;
  Printf.printf " - Done\n")

let local_python_code =
    "from coccinelle import *\n"

let python_code =
  "import coccinelle\n"^
    "import coccilib\n"^
    "import coccilib.org\n"^
    "import coccilib.report\n" ^
    local_python_code ^
    "cocci = Cocci()\n"

let make_init lang code rule_info =
  let mv = [] in
  {
  scr_ast_rule = (lang, mv, [], code);
  language = lang;
  script_code = (if lang = "python" then python_code else "") ^code;
  scr_rule_info = rule_info;
}

(* --------------------------------------------------------------------- *)
let prepare_cocci ctls free_var_lists negated_pos_lists
    (ua,fua,fuas) positions_list metavars astcocci =

  let gathered = Common.index_list_1
      (zip (zip (zip (zip (zip (zip (zip (zip ctls metavars) astcocci)
				  free_var_lists)
		   negated_pos_lists) ua) fua) fuas) positions_list)
  in
  gathered +> List.map
    (fun (((((((((ctl_toplevel_list,metavars),ast),free_var_list),
	     negated_pos_list),ua),fua),fuas),positions_list),rulenb) ->

      let build_rule_info rulename deps =
	{rulename = rulename;
	  dependencies = deps;
	  used_after = (List.hd ua) @ (List.hd fua);
	  ruleid = rulenb;
	  was_matched = ref false;} in

      let is_script_rule r =
        match r with
	  Ast_cocci.ScriptRule _
	| Ast_cocci.InitialScriptRule _ | Ast_cocci.FinalScriptRule _ -> true
	| _ -> false in

      if not (List.length ctl_toplevel_list =|= 1) && not (is_script_rule ast)
      then failwith "not handling multiple minirules";

      match ast with
        Ast_cocci.ScriptRule (name,lang,deps,mv,script_vars,code) ->
          let r =
            {
	      scr_ast_rule = (lang, mv, script_vars, code);
              language = lang;
              script_code = code;
              scr_rule_info = build_rule_info name deps;
	    }
          in ScriptRuleCocciInfo r
      | Ast_cocci.InitialScriptRule (name,lang,deps,code) ->
	  let r = make_init lang code (build_rule_info name deps) in
	    InitialScriptRuleCocciInfo r
      | Ast_cocci.FinalScriptRule (name,lang,deps,code) ->
	  let mv = [] in
          let r =
            {
              scr_ast_rule = (lang, mv, [], code);
              language = lang;
              script_code = code;
              scr_rule_info = build_rule_info name deps;
            }
          in FinalScriptRuleCocciInfo r
      | Ast_cocci.CocciRule
	  (rulename,(dependencies,dropped_isos,z),restast,isexp,ruletype) ->
            CocciRuleCocciInfo (
            {
              ctl = List.hd ctl_toplevel_list;
              metavars = metavars;
              ast_rule = ast;
	      isexp = List.hd isexp;
              dropped_isos = dropped_isos;
              free_vars = List.hd free_var_list;
              negated_pos_vars = List.hd negated_pos_list;
              positions = List.hd positions_list;
	      ruletype = ruletype;
	      rule_info = build_rule_info rulename dependencies;
            })
    )

(* --------------------------------------------------------------------- *)

let build_info_program cprogram env =

  let (cs, parseinfos) =
    Common.unzip cprogram in

  let alltoks =
    parseinfos +> List.map (fun (s,toks) -> toks) +> List.flatten in

  (* I use cs' but really annotate_xxx work by doing side effects on cs *)
  let cs' =
    Comment_annotater_c.annotate_program alltoks cs in
  let cs_with_envs =
    Type_annoter_c.annotate_program env (*!g_contain_typedmetavar*) cs'
  in

  zip cs_with_envs parseinfos +> List.map (fun ((c, (enva,envb)), parseinfo)->
    let (fullstr, tokens) = parseinfo in

    let flow =
      ast_to_flow_with_error_messages c +>
      Common.map_option (fun flow ->
        let flow = Ast_to_flow.annotate_loop_nodes flow in

        (* remove the fake nodes for julia *)
        let fixed_flow = CCI.fix_flow_ctl flow in

        if !Flag_cocci.show_flow then print_flow fixed_flow;
        if !Flag_cocci.show_before_fixed_flow then print_flow flow;

        fixed_flow
      )
    in

    {
      ast_c = c; (* contain refs so can be modified *)
      tokens_c =  tokens;
      fullstring = fullstr;

      flow = flow;

      contain_loop = contain_loop flow;

      env_typing_before = enva;
      env_typing_after = envb;

      was_modified = ref false;
    }
  )



(* Optimisation. Try not unparse/reparse the whole file when have modifs  *)
let rebuild_info_program cs file isexp =
  cs +> List.map (fun c ->
    if !(c.was_modified)
    then
      let file = Common.new_temp_file "cocci_small_output" ".c" in
      cfile_of_program
        [(c.ast_c, (c.fullstring, c.tokens_c)), Unparse_c.PPnormal]
        file;

      (* Common.command2 ("cat " ^ file); *)
      let cprogram = cprogram_of_file file in
      let xs = build_info_program cprogram c.env_typing_before in

      (* TODO: assert env has not changed,
      * if yes then must also reparse what follows even if not modified.
      * Do that only if contain_typedmetavar of course, so good opti.
      *)
      (* Common.list_init xs *) (* get rid of the FinalDef *)
      xs
    else [c]
  ) +> List.concat


let rebuild_info_c_and_headers ccs isexp =
  ccs +> List.iter (fun c_or_h ->
    if c_or_h.asts +> List.exists (fun c -> !(c.was_modified))
    then c_or_h.was_modified_once := true;
  );
  ccs +> List.map (fun c_or_h ->
    { c_or_h with
      asts =
      rebuild_info_program c_or_h.asts c_or_h.full_fname isexp }
  )

let rec prepare_h seen env hpath choose_includes : file_info list =
  if not (Common.lfile_exists hpath)
  then
    begin
      pr2 ("TYPE: header " ^ hpath ^ " not found");
      []
    end
  else
    begin
      let h_cs = cprogram_of_file_cached hpath in
      let local_includes =
	if choose_includes =*= Flag_cocci.I_REALLY_ALL_INCLUDES
	then
	  List.filter
	    (function x -> not (List.mem x !seen))
	    (includes_to_parse [(hpath,h_cs)] choose_includes)
	else [] in
      seen := local_includes @ !seen;
      let others =
	List.concat
	  (List.map (function x -> prepare_h seen env x choose_includes)
	     local_includes) in
      let info_h_cs = build_info_program h_cs !env in
      env :=
	if null info_h_cs
	then !env
	else last_env_toplevel_c_info info_h_cs;
      others@
      [{
	fname = Common.basename hpath;
	full_fname = hpath;
	asts = info_h_cs;
	was_modified_once = ref false;
	fpath = hpath;
	fkind = Header;
      }]
    end

let prepare_c files choose_includes : file_info list =
  let cprograms = List.map cprogram_of_file_cached files in
  let includes = includes_to_parse (zip files cprograms) choose_includes in
  let seen = ref includes in

  (* todo?: may not be good to first have all the headers and then all the c *)
  let env = ref !TAC.initial_env in

  let includes =
    includes +>
    List.map (function hpath -> prepare_h seen env hpath choose_includes) +>
    List.concat in

  let cfiles =
    (zip files cprograms) +>
    List.map
      (function (file, cprogram) ->
      (* todo?: don't update env ? *)
        let cs = build_info_program cprogram !env in
        (* we do that only for the c, not for the h *)
        ignore(update_include_rel_pos (cs +> List.map (fun x -> x.ast_c)));
        {
        fname = Common.basename file;
        full_fname = file;
        asts = cs;
        was_modified_once = ref false;
        fpath = file;
        fkind = Source
      }) in

  includes @ cfiles

(*****************************************************************************)
(* Processing the ctls and toplevel C elements *)
(*****************************************************************************)

(* The main algorithm =~
 * The algorithm is roughly:
 *  for_all ctl rules in SP
 *   for_all minirule in rule (no more)
 *    for_all binding (computed during previous phase)
 *      for_all C elements
 *         match control flow of function vs minirule
 *         with the binding and update the set of possible
 *         bindings, and returned the possibly modified function.
 *   pretty print modified C elements and reparse it.
 *
 *
 * On ne prends que les newbinding ou returned_any_state est vrai.
 * Si ca ne donne rien, on prends ce qu'il y avait au depart.
 * Mais au nouveau depart de quoi ?
 * - si ca donne rien apres avoir traité toutes les fonctions avec ce binding ?
 * - ou alors si ca donne rien, apres avoir traité toutes les fonctions
 *   avec tous les bindings du round d'avant ?
 *
 * Julia pense qu'il faut prendre la premiere solution.
 * Example: on a deux environnements candidats, E1 et E2 apres avoir traité
 * la regle ctl 1. On arrive sur la regle ctl 2.
 * E1 ne donne rien pour la regle 2, on garde quand meme E1 pour la regle 3.
 * E2 donne un match a un endroit et rend E2' alors on utilise ca pour
 * la regle 3.
 *
 * I have not to look at used_after_list to decide to restart from
 * scratch. I just need to look if the binding list is empty.
 * Indeed, let's suppose that a SP have 3 regions/rules. If we
 * don't find a match for the first region, then if this first
 * region does not bind metavariable used after, that is if
 * used_after_list is empty, then mysat(), even if does not find a
 * match, will return a Left, with an empty transformation_info,
 * and so current_binding will grow. On the contrary if the first
 * region must bind some metavariables used after, and that we
 * dont find any such region, then mysat() will returns lots of
 * Right, and current_binding will not grow, and so we will have
 * an empty list of binding, and we will catch such a case.
 *
 * opti: julia says that because the binding is
 * determined by the used_after_list, the items in the list
 * are kind of sorted, so could optimise the insert_set operations.
 *)


(* r(ule), c(element in C code), e(nvironment) *)

let findk f l =
  let rec loop k = function
      [] -> None
    | x::xs ->
	if f x
	then Some (x, function n -> k (n :: xs))
	else loop (function vs -> k (x :: vs)) xs in
  loop (function x -> x) l

let merge_env new_e old_e =
  let (ext,old_e) =
    List.fold_left
      (function (ext,old_e) ->
	function (e,rules) as elem ->
	  match findk (function (e1,_) -> e =*= e1) old_e with
	    None -> (elem :: ext,old_e)
	  | Some((_,old_rules),k) ->
	      (ext,k (e,Common.union_set rules old_rules)))
      ([],old_e) new_e in
  old_e @ (List.rev ext)

let contains_binding e (_,(r,m),_) =
  try
    let _ = List.find (function ((re, rm), _) -> r =*= re && m =$= rm) e in
    true
  with Not_found -> false

let python_application mv ve script_vars r =
  let mv =
    List.map
      (function
	  ((Some x,None),y,z) -> (x,y,z)
	| _ ->
	    failwith
	      (Printf.sprintf "unexpected ast metavar in rule %s"
		 r.scr_rule_info.rulename))
      mv in
  try
    Pycocci.build_classes (List.map (function (x,y) -> x) ve);
    Pycocci.construct_variables mv ve;
    Pycocci.construct_script_variables script_vars;
    let _ = Pycocci.pyrun_simplestring (local_python_code ^r.script_code) in
    if !Pycocci.inc_match
    then Some (Pycocci.retrieve_script_variables script_vars)
    else None
  with Pycocci.Pycocciexception ->
    (pr2 ("Failure in " ^ r.scr_rule_info.rulename);
     raise Pycocci.Pycocciexception)

let ocaml_application mv ve script_vars r =
  try
    let script_vals =
      Run_ocamlcocci.run mv ve script_vars
	r.scr_rule_info.rulename r.script_code in
    if !Coccilib.inc_match
    then Some script_vals
    else None
  with e -> (pr2 ("Failure in " ^ r.scr_rule_info.rulename); raise e)

let apply_script_rule r cache newes e rules_that_have_matched
    rules_that_have_ever_matched script_application =
  Common.profile_code r.language (fun () ->
  show_or_not_scr_rule_name r.scr_rule_info.ruleid;
  if not(interpret_dependencies rules_that_have_matched
	   !rules_that_have_ever_matched r.scr_rule_info.dependencies)
  then
    begin
      print_dependencies "dependencies for script not satisfied:"
	rules_that_have_matched
	!rules_that_have_ever_matched r.scr_rule_info.dependencies;
      show_or_not_binding "in environment" e;
      (cache, (e, rules_that_have_matched)::newes)
    end
  else
    begin
      let (_, mv, script_vars, _) = r.scr_ast_rule in
      let ve =
	(List.map (function (n,v) -> (("virtual",n),Ast_c.MetaIdVal (v,[])))
	   !Flag.defined_virtual_env) @ e in
      let not_bound x = not (contains_binding ve x) in
      (match List.filter not_bound mv with
	[] ->
	  let relevant_bindings =
	    List.filter
	      (function ((re,rm),_) ->
		List.exists (function (_,(r,m),_) -> r =*= re && m =$= rm) mv)
	      e in
	  (try
	    match List.assoc relevant_bindings cache with
	      None -> (cache,newes)
	    | Some script_vals ->
		print_dependencies
		  "dependencies for script satisfied, but cached:"
		  rules_that_have_matched
		  !rules_that_have_ever_matched
		  r.scr_rule_info.dependencies;
		show_or_not_binding "in" e;
	      (* env might be bigger than what was cached against, so have to
		 merge with newes anyway *)
		let new_e = (List.combine script_vars script_vals) @ e in
		let new_e =
		  new_e +>
		  List.filter
		    (fun (s,v) -> List.mem s r.scr_rule_info.used_after) in
		(cache,merge_env [(new_e, rules_that_have_matched)] newes)
	  with Not_found ->
	    begin
	      print_dependencies "dependencies for script satisfied:"
		rules_that_have_matched
		!rules_that_have_ever_matched
		r.scr_rule_info.dependencies;
	      show_or_not_binding "in" e;
	      match script_application mv ve script_vars r with
		None ->
		  (* failure means we should drop e, no new bindings *)
		  (((relevant_bindings,None) :: cache), newes)
	      | Some script_vals ->
		  let script_vals =
		    List.map (function x -> Ast_c.MetaIdVal(x,[]))
		      script_vals in
		  let new_e =
		    (List.combine script_vars script_vals) @ e in
		  let new_e =
		    new_e +>
		    List.filter
		      (fun (s,v) -> List.mem s r.scr_rule_info.used_after) in
		  r.scr_rule_info.was_matched := true;
		  (((relevant_bindings,Some script_vals) :: cache),
		   merge_env
		     [(new_e,
		       r.scr_rule_info.rulename :: rules_that_have_matched)]
		     newes)
	    end)
      |	unbound ->
	  (if !Flag_cocci.show_dependencies
	  then
	    let m2c (_,(r,x),_) = r^"."^x in
	    pr2 (Printf.sprintf "script not applied: %s not bound"
		   (String.concat ", " (List.map m2c unbound))));
	  let e =
	    e +>
	    List.filter
	      (fun (s,v) -> List.mem s r.scr_rule_info.used_after) in
	  (cache, merge_env [(e, rules_that_have_matched)] newes))
    end)

let rec apply_cocci_rule r rules_that_have_ever_matched es
    (ccs:file_info list ref) =
  Common.profile_code r.rule_info.rulename (fun () ->
    show_or_not_rule_name r.ast_rule r.rule_info.ruleid;
    show_or_not_ctl_text r.ctl r.ast_rule r.rule_info.ruleid;

    let reorganized_env =
      reassociate_positions r.free_vars r.negated_pos_vars !es in

    (* looping over the environments *)
    let (_,newes (* envs for next round/rule *)) =
      List.fold_left
	(function (cache,newes) ->
	  function ((e,rules_that_have_matched),relevant_bindings) ->
	    if not(interpret_dependencies rules_that_have_matched
		     !rules_that_have_ever_matched
		     r.rule_info.dependencies)
	    then
	      begin
		print_dependencies
		  ("dependencies for rule "^r.rule_info.rulename^
		   " not satisfied:")
		  rules_that_have_matched
		  !rules_that_have_ever_matched r.rule_info.dependencies;
		show_or_not_binding "in environment" e;
		(cache,
		 merge_env
		   [(e +>
		     List.filter
		       (fun (s,v) -> List.mem s r.rule_info.used_after),
		     rules_that_have_matched)]
		   newes)
	      end
	    else
	      let new_bindings =
		try List.assoc relevant_bindings cache
		with
		  Not_found ->
		    print_dependencies
		      ("dependencies for rule "^r.rule_info.rulename^
		       " satisfied:")
		      rules_that_have_matched
		      !rules_that_have_ever_matched
		      r.rule_info.dependencies;
		    show_or_not_binding "in" e;
		    show_or_not_binding "relevant in" relevant_bindings;

		    (* applying the rule *)
		    (match r.ruletype with
		      Ast_cocci.Normal ->
                      (* looping over the functions and toplevel elements in
			 .c and .h *)
			List.rev
			  (concat_headers_and_c !ccs +>
			   List.fold_left (fun children_e (c,f) ->
			     if c.flow <> None
			     then
                             (* does also some side effects on c and r *)
			       let processed =
				 process_a_ctl_a_env_a_toplevel r
				   relevant_bindings c f in
			       match processed with
			       | None -> children_e
			       | Some newbindings ->
				   newbindings +>
				   List.fold_left
				     (fun children_e newbinding ->
				       if List.mem newbinding children_e
				       then children_e
				       else newbinding :: children_e)
				     children_e
			     else children_e)
			     [])
		    | Ast_cocci.Generated ->
			process_a_generated_a_env_a_toplevel r
			  relevant_bindings !ccs;
			[]) in

	      let old_bindings_to_keep =
		Common.nub
		  (e +>
		   List.filter
		     (fun (s,v) -> List.mem s r.rule_info.used_after)) in
	      let new_e =
		if null new_bindings
		then
		  begin
		  (*use the old bindings, specialized to the used_after_list*)
		    if !Flag_ctl.partial_match
		    then
		      printf
			"Empty list of bindings, I will restart from old env\n";
		    [(old_bindings_to_keep,rules_that_have_matched)]
		  end
		else
		(* combine the new bindings with the old ones, and
		   specialize to the used_after_list *)
		  let old_variables = List.map fst old_bindings_to_keep in
		  (* have to explicitly discard the inherited variables
		     because we want the inherited value of the positions
		     variables not the extended one created by
		     reassociate_positions. want to reassociate freshly
		     according to the free variables of each rule. *)
		  let new_bindings_to_add =
		    Common.nub
		      (new_bindings +>
		       List.map
			 (List.filter
			    (function
				(* see comment before combine_pos *)
				(s,Ast_c.MetaPosValList []) -> false
			      |	(s,v) ->
				  List.mem s r.rule_info.used_after &&
				  not (List.mem s old_variables)))) in
		  List.map
		    (function new_binding_to_add ->
		      (List.sort compare
			 (Common.union_set
			    old_bindings_to_keep new_binding_to_add),
		       r.rule_info.rulename::rules_that_have_matched))
		    new_bindings_to_add in
	      ((relevant_bindings,new_bindings)::cache,
	       merge_env new_e newes))
	([],[]) reorganized_env in (* end iter es *)
    if !(r.rule_info.was_matched)
    then Common.push2 r.rule_info.rulename rules_that_have_ever_matched;

    es := newes;

    (* apply the tagged modifs and reparse *)
    if not !Flag.sgrep_mode2
    then ccs := rebuild_info_c_and_headers !ccs r.isexp)

and reassociate_positions free_vars negated_pos_vars envs =
  (* issues: isolate the bindings that are relevant to a given rule.
     separate out the position variables
     associate all of the position variables for a given set of relevant
     normal variable bindings with each set of relevant normal variable
     bindings.  Goal: if eg if@p (E) matches in two places, then both inherited
     occurrences of E should see both bindings of p, not just its own.
     Otherwise, a position constraint for something that matches in two
     places will never be useful, because the position can always be
     different from the other one. *)
   let relevant =
     List.map
       (function (e,_) ->
	 List.filter (function (x,_) -> List.mem x free_vars) e)
       envs in
   let splitted_relevant =
     (* separate the relevant variables into the non-position ones and the
	position ones *)
     List.map
       (function r ->
	 List.fold_left
	   (function (non_pos,pos) ->
	     function (v,_) as x ->
	       if List.mem v negated_pos_vars
	       then (non_pos,x::pos)
	       else (x::non_pos,pos))
	   ([],[]) r)
       relevant in
   let splitted_relevant =
     List.map
       (function (non_pos,pos) ->
	 (List.sort compare non_pos,List.sort compare pos))
       splitted_relevant in
   let non_poss =
     List.fold_left
       (function non_pos ->
	 function (np,_) ->
	   if List.mem np non_pos then non_pos else np::non_pos)
       [] splitted_relevant in
   let extended_relevant =
     (* extend the position variables with the values found at other identical
	variable bindings *)
     List.map
       (function non_pos ->
	 let others =
	   List.filter
	     (function (other_non_pos,other_pos) ->
               (* do we want equal? or just somehow compatible? eg non_pos
	       binds only E, but other_non_pos binds both E and E1 *)
	       non_pos =*= other_non_pos)
	     splitted_relevant in
	 (non_pos,
	  List.sort compare
	    (non_pos @
	     (combine_pos negated_pos_vars
		(List.map (function (_,x) -> x) others)))))
       non_poss in
   List.combine envs
     (List.map (function (non_pos,_) -> List.assoc non_pos extended_relevant)
	splitted_relevant)

(* If the negated posvar is not bound at all, this function will
nevertheless bind it to [].  If we get rid of these bindings, then the
matching of the term the position variable with the constraints will fail
because some variables are unbound.  So we let the binding be [] and then
we will have to clean these up afterwards.  This should be the only way
that a position variable can have an empty binding. *)
and combine_pos negated_pos_vars others =
  List.map
    (function posvar ->
      let positions =
	List.sort compare
	  (List.fold_left
	     (function positions ->
	       function other_list ->
		 try
		   match List.assoc posvar other_list with
		     Ast_c.MetaPosValList l1 ->
		       Common.union_set l1 positions
		   | _ -> failwith "bad value for a position variable"
		 with Not_found -> positions)
	     [] others) in
      (posvar,Ast_c.MetaPosValList positions))
    negated_pos_vars

and process_a_generated_a_env_a_toplevel2 r env = function
    [cfile] ->
      let free_vars =
	List.filter
	  (function
	      (rule,_) when rule =$= r.rule_info.rulename -> false
	    | (_,"ARGS") -> false
	    | _ -> true)
	  r.free_vars in
      let env_domain = List.map (function (nm,vl) -> nm) env in
      let metavars =
	List.filter
	  (function md ->
	    let (rl,_) = Ast_cocci.get_meta_name md in rl =$= r.rule_info.rulename)
	  r.metavars in
      if Common.include_set free_vars env_domain
      then Unparse_hrule.pp_rule metavars r.ast_rule env cfile.full_fname
  | _ -> failwith "multiple files not supported"

and process_a_generated_a_env_a_toplevel rule env ccs =
  Common.profile_code "process_a_ctl_a_env_a_toplevel"
    (fun () -> process_a_generated_a_env_a_toplevel2 rule env ccs)

(* does side effects on C ast and on Cocci info rule *)
and process_a_ctl_a_env_a_toplevel2 r e c f =
 indent_do (fun () ->
  show_or_not_celem "trying" c.ast_c;
  Flag.currentfile := Some (f ^ ":" ^get_celem c.ast_c);
  let (trans_info, returned_any_states, inherited_bindings, newbindings) =
    Common.save_excursion Flag_ctl.loop_in_src_code (fun () ->
      Flag_ctl.loop_in_src_code := !Flag_ctl.loop_in_src_code||c.contain_loop;

      (***************************************)
      (* !Main point! The call to the engine *)
      (***************************************)
      let model_ctl  = CCI.model_for_ctl r.dropped_isos (Common.some c.flow) e
      in CCI.mysat model_ctl r.ctl (r.rule_info.used_after, e)
    )
  in
  if not returned_any_states
  then None
  else begin
    show_or_not_celem "found match in" c.ast_c;
    show_or_not_trans_info trans_info;
    List.iter (show_or_not_binding "out") newbindings;

    r.rule_info.was_matched := true;

    if not (null trans_info) &&
      not (!Flag.sgrep_mode2 && not !Flag_cocci.show_diff)
    then begin
      c.was_modified := true;
      try
        (* les "more than one var in a decl" et "already tagged token"
         * font crasher coccinelle. Si on a 5 fichiers, donc on a 5
         * failed. Le try limite le scope des crashes pendant la
         * trasformation au fichier concerne. *)

        (* modify ast via side effect *)
        ignore(Transformation_c.transform r.rule_info.rulename r.dropped_isos
                  inherited_bindings trans_info (Common.some c.flow));
      with Timeout -> raise Timeout | UnixExit i -> raise (UnixExit i)
    end;

    Some (List.map (function x -> x@inherited_bindings) newbindings)
  end
 )

and process_a_ctl_a_env_a_toplevel  a b c f=
  Common.profile_code "process_a_ctl_a_env_a_toplevel"
    (fun () -> process_a_ctl_a_env_a_toplevel2 a b c f)


let rec bigloop2 rs (ccs: file_info list) =
  let init_es = [(Ast_c.emptyMetavarsBinding,[])] in
  let es = ref init_es in
  let ccs = ref ccs in
  let rules_that_have_ever_matched = ref [] in

  (* looping over the rules *)
  rs +> List.iter (fun r ->
    match r with
      InitialScriptRuleCocciInfo r | FinalScriptRuleCocciInfo r -> ()
    | ScriptRuleCocciInfo r ->
	if !Flag_cocci.show_ctl_text then begin
          Common.pr_xxxxxxxxxxxxxxxxx ();
          pr ("script: " ^ r.language);
          Common.pr_xxxxxxxxxxxxxxxxx ();

          adjust_pp_with_indent (fun () ->
            Format.force_newline();
            let (l,mv,script_vars,code) = r.scr_ast_rule in
	    let nm = r.scr_rule_info.rulename in
	    let deps = r.scr_rule_info.dependencies in
            Pretty_print_cocci.unparse
	      (Ast_cocci.ScriptRule (nm,l,deps,mv,script_vars,code)));
	end;

	if !Flag.show_misc then print_endline "RESULT =";

        let (_, newes) =
          List.fold_left
            (function (cache, newes) ->
              function (e, rules_that_have_matched) ->
		match r.language with
                  "python" ->
		    apply_script_rule r cache newes e rules_that_have_matched
		      rules_that_have_ever_matched python_application
                | "ocaml" ->
		    apply_script_rule r cache newes e rules_that_have_matched
		      rules_that_have_ever_matched ocaml_application
		| "test" ->
		    concat_headers_and_c !ccs +> List.iter (fun (c,_) ->
		      if c.flow <> None
		      then
			Printf.printf "Flow: %s\r\nFlow!\r\n%!" c.fullstring);
		    (cache, newes)
		| _ ->
                    Printf.printf "Unknown language: %s\n" r.language;
                    (cache, newes))
            ([],[]) !es in

	(if !(r.scr_rule_info.was_matched)
	then
	  Common.push2 r.scr_rule_info.rulename rules_that_have_ever_matched);

        es := newes (*(if newes = [] then init_es else newes)*);
    | CocciRuleCocciInfo r ->
	apply_cocci_rule r rules_that_have_ever_matched
	  es ccs);

  if !Flag.sgrep_mode2
  then begin
    (* sgrep can lead to code that is not parsable, but we must
     * still call rebuild_info_c_and_headers to pretty print the
     * action (MINUS), so that later the diff will show what was
     * matched by sgrep. But we don't want the parsing error message
     * hence the following flag setting. So this code propably
     * will generate a NotParsedCorrectly for the matched parts
     * and the very final pretty print and diff will work
     *)
    Flag_parsing_c.verbose_parsing := false;
    ccs := rebuild_info_c_and_headers !ccs false
  end;
  !ccs (* return final C asts *)

let bigloop a b =
  Common.profile_code "bigloop" (fun () -> bigloop2 a b)

type init_final = Initial | Final

let initial_final_bigloop2 ty rebuild r =
  if !Flag_cocci.show_ctl_text then
    begin
      Common.pr_xxxxxxxxxxxxxxxxx ();
      pr ((match ty with Initial -> "initial" | Final -> "final") ^ ": " ^
	  r.language);
      Common.pr_xxxxxxxxxxxxxxxxx ();

      adjust_pp_with_indent (fun () ->
	Format.force_newline();
	Pretty_print_cocci.unparse(rebuild r.scr_ast_rule r.scr_rule_info.dependencies));
    end;

  match r.language with
    "python" ->
      (* include_match makes no sense in an initial or final rule, although
	 we have no way to prevent it *)
      let _ = apply_script_rule r [] [] [] [] (ref []) python_application in
      ()
  | "ocaml" when ty = Initial -> () (* nothing to do *)
  | "ocaml" ->
      (* include_match makes no sense in an initial or final rule, although
	 we have no way to prevent it *)
      let _ = apply_script_rule r [] [] [] [] (ref []) ocaml_application in
      ()
  | _ ->
      failwith ("Unknown language for initial/final script: "^
		r.language)

let initial_final_bigloop a b c =
  Common.profile_code "initial_final_bigloop"
    (fun () -> initial_final_bigloop2 a b c)

(*****************************************************************************)
(* The main functions *)
(*****************************************************************************)

let pre_engine2 (coccifile, isofile) =
  show_or_not_cocci coccifile isofile;
  Pycocci.set_coccifile coccifile;

  let isofile =
    if not (Common.lfile_exists isofile)
    then begin
      pr2 ("warning: Can't find default iso file: " ^ isofile);
      None
    end
    else Some isofile in

  (* useful opti when use -dir *)
  let (metavars,astcocci,
       free_var_lists,negated_pos_lists,used_after_lists,
       positions_lists,(toks,_,_)) =
      sp_of_file coccifile isofile in
  let ctls = ctls_of_ast astcocci used_after_lists positions_lists in

  g_contain_typedmetavar := sp_contain_typed_metavar astcocci;

  check_macro_in_sp_and_adjust toks;

  show_or_not_ctl_tex astcocci ctls;

  let cocci_infos =
    prepare_cocci ctls free_var_lists negated_pos_lists
      used_after_lists positions_lists metavars astcocci in

  let used_languages =
    List.fold_left
      (function languages ->
	 function
	     ScriptRuleCocciInfo(r) ->
	       if List.mem r.language languages then
		 languages
	       else
		 r.language::languages
	   | _ -> languages)
      [] cocci_infos in

  let initialized_languages =
    List.fold_left
      (function languages ->
	 function
	     InitialScriptRuleCocciInfo(r) ->
	       (if List.mem r.language languages
		then
		 failwith
		   ("double initializer found for "^r.language));
	       if interpret_dependencies [] [] r.scr_rule_info.dependencies
	       then
		 begin
		   initial_final_bigloop Initial
		     (fun (x,_,_,y) -> fun deps ->
		       Ast_cocci.InitialScriptRule(r.scr_rule_info.rulename,x,deps,y))
		     r;
		   r.language::languages
		 end
	       else languages
	   | _ -> languages)
      [] cocci_infos in

  let uninitialized_languages =
    List.filter
      (fun used -> not (List.mem used initialized_languages))
      used_languages in
  List.iter
    (fun lgg ->
      let rule_info =
      	{rulename = "";
	  dependencies = Ast_cocci.NoDep;
	  used_after = [];
	  ruleid = (-1);
	  was_matched = ref false;} in
      initial_final_bigloop Initial
	(fun (x,_,_,y) -> fun deps ->
	  Ast_cocci.InitialScriptRule("",x,deps,y))
	(make_init lgg "" rule_info))
    uninitialized_languages;

  (cocci_infos,toks)

let pre_engine a =
  Common.profile_code "pre_engine" (fun () -> pre_engine2 a)

let full_engine2 (cocci_infos,toks) cfiles =

  show_or_not_cfiles  cfiles;

  (* optimisation allowing to launch coccinelle on all the drivers *)
  if !Flag_cocci.worth_trying_opt && not (worth_trying cfiles toks)
  then
    begin
      (match toks with
	None -> ()
      | Some toks ->
	  pr2 ("No matches found for " ^ (Common.join " " toks)
	       ^ "\nSkipping:" ^ (Common.join " " cfiles)));
      cfiles +> List.map (fun s -> s, None)
    end
  else
    begin

      if !Flag.show_misc then Common.pr_xxxxxxxxxxxxxxxxx();
      if !Flag.show_misc then pr "let's go";
      if !Flag.show_misc then Common.pr_xxxxxxxxxxxxxxxxx();

      let choose_includes =
	match !Flag_cocci.include_options with
	  Flag_cocci.I_UNSPECIFIED ->
	    if !g_contain_typedmetavar
	    then Flag_cocci.I_NORMAL_INCLUDES
	    else Flag_cocci.I_NO_INCLUDES
	| x -> x in
      let c_infos  = prepare_c cfiles choose_includes in

      (* ! the big loop ! *)
      let c_infos' = bigloop cocci_infos c_infos in

      if !Flag.show_misc then Common.pr_xxxxxxxxxxxxxxxxx ();
      if !Flag.show_misc then pr "Finished";
      if !Flag.show_misc then Common.pr_xxxxxxxxxxxxxxxxx ();
      if !Flag_ctl.graphical_trace then gen_pdf_graph ();

      c_infos' +> List.map (fun c_or_h ->
	if !(c_or_h.was_modified_once)
	then
	  begin
            let outfile =
	      Common.new_temp_file "cocci-output" ("-" ^ c_or_h.fname) in

            if c_or_h.fkind =*= Header
            then pr2 ("a header file was modified: " ^ c_or_h.fname);

            (* and now unparse everything *)
            cfile_of_program (for_unparser c_or_h.asts) outfile;

            show_or_not_diff c_or_h.fpath outfile;

            (c_or_h.fpath,
             if !Flag.sgrep_mode2 then None else Some outfile)
	  end
	else (c_or_h.fpath, None))
    end

let full_engine a b =
  Common.profile_code "full_engine"
    (fun () -> let res = full_engine2 a b in (*Gc.print_stat stderr; *)res)

let post_engine2 (cocci_infos,_) =
  let _ =
    List.fold_left
      (function languages ->
	function
	    FinalScriptRuleCocciInfo(r) ->
	      (if List.mem r.language languages
	      then failwith ("double finalizer found for "^r.language));
	      initial_final_bigloop Final
		(fun (x,_,_,y) -> fun deps ->
		  Ast_cocci.FinalScriptRule(r.scr_rule_info.rulename,x,deps,y))
		r;
	      r.language::languages
	  | _ -> languages)
      [] cocci_infos in
  ()

let post_engine a =
  Common.profile_code "post_engine" (fun () -> post_engine2 a)

(*****************************************************************************)
(* check duplicate from result of full_engine *)
(*****************************************************************************)

let check_duplicate_modif2 xs =
  (* opti: let groups = Common.groupBy (fun (a,resa) (b,resb) -> a =$= b) xs *)
  if !Flag_cocci.verbose_cocci
  then pr2 ("Check duplication for " ^ i_to_s (List.length xs) ^ " files");

  let groups = Common.group_assoc_bykey_eff xs in
  groups +> Common.map_filter (fun (file, xs) ->
    match xs with
    | [] -> raise Impossible
    | [res] -> Some (file, res)
    | res::xs ->
        match res with
        | None ->
            if not (List.for_all (fun res2 -> res2 =*= None) xs)
            then begin
              pr2 ("different modification result for " ^ file);
              None
            end
            else Some (file, None)
        | Some res ->
            if not(List.for_all (fun res2 ->
              match res2 with
              | None -> false
              | Some res2 ->
                  let diff = Common.cmd_to_list ("diff -u -b -B "^res^" "^res2)
                  in
                  null diff
            ) xs) then begin
              pr2 ("different modification result for " ^ file);
              None
            end
            else Some (file, Some res)
  )
let check_duplicate_modif a =
  Common.profile_code "check_duplicate" (fun () -> check_duplicate_modif2 a)
