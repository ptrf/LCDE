(* Copyright 2010, Peter Tersløv Forsberg, ptrf@diku.dk *)

open Infixes
module C = Context
module D = Deckard_types
module L = Lib_parsing_c
module A = Ast_c
module P = Process

let prepare_merge () =
    let files = List.fold_left
               (fun x y -> if List.mem y x then x else y::x)
             [] (List.map fst !C.vseq)
    in
    let same_name name (x,_) = name = x
    in
    List.map (fun name ->
      (name, (List.map snd (List.filter (same_name name) !C.vseq))))
             files

let get_pos item =
    let info = (match item with
    | D.Statement s ->
            L.ii_of_stmt s
    | D.Declaration d ->
            L.ii_of_decl d
    | D.Definition d ->
            L.ii_of_toplevel (A.Definition d)
    | D.Cpp_directive d ->
            L.ii_of_toplevel (A.CppTop d)
    | D.Ifdef_directive d ->
            L.ii_of_toplevel (A.IfdefTop d)
    | D.Expression _ -> failwith ( "If this happens, we merge below statement" ^
    "level, which is currently not supported" )
    ) in
    let (_,_,s,e) =
        L.lin_col_by_pos info in
    (s,e)

let compare_pos x y =
    let ((slx,scx),(elx,ecx)) = get_pos x in
    let ((sly,scy),(ely,ecy)) = get_pos y in
    if slx = sly then
        (* check whether they start on same column *)
        if scx = scy then
            (* check whether they end on the same line *)
            (* note that since we are checking where they end, one has to be
             * contained within the other *)
            if elx = ely then
                if ecx = ecy then
                    raise (C.ImpossiblePos "two vectors have the same position")
                else compare ecy ecx
            else compare ely elx
        else
            compare scx scy
    else
        compare slx sly

let sequentialize store =
    (* quick hack - get rid of empty exprStatements *)
    let pruned = List.filter (fun ((_,x),_) -> try let _ = get_pos x in true with
    _ -> false) store in
    List.sort (fun ((_,x),_) ((_,y),_) -> compare_pos x y) pruned

let rec get_next_window l w s xs =
    (take l w s xs,move l w s xs)

and merge_window l w s items =
    let (cur,rem) = get_next_window l w s items in
    if (List.length cur) < 2 then () else
    let acc_vector = List.fold_left (fun x (y,_) -> x +: y) [] cur in
    let node_list = List.map snd cur in
    P.store node_list acc_vector;
    if rem <> [] then
        merge_window l w s rem
    else ()

and merge_simple width stride level ordered =
    merge_window level width stride ordered

and take n w s xs =
    let mytake = take n in
    if w < 1 then []
    else match xs with
    | (v,l)::rs ->
            if l < n then []
            else
                if l = n then v::(mytake (w-1) s rs)
                else (
                    merge_simple w s l xs;
                    mytake w s (proceed_to_next n rs))
    | [] -> []

and proceed_to_next level xs =
    let myproceed = proceed_to_next level in
    match xs with
    | (_,l)::rs ->      if l > level then myproceed rs
                   else if l = level then xs
                   else []
    | [] -> []

and move_normal level s xs =
    let mymove = move_normal level in
    if s < 1 then
        match xs with
        | (_,l)::rs -> if l > level then (proceed_to_next level rs)
                       else xs
        | [] -> []
    else match xs with
    | (_,l)::rs ->      if l > level then mymove s rs
                   else if l = level then mymove (s-1) rs
                   else []
    | [] -> []


and move level w s xs =
    let sw_equal = w = s in
    match xs with
    | (_,l)::_ ->
            if l>level then if sw_equal then
                 merge_simple w s l xs;
                 move_normal level s xs
    | [] -> []

let merge_ordered xs =
    merge_simple !C.width !C.stride 1 xs

let merge () =
    let ordered_by_file = prepare_merge () in
    let sequentialized = List.map (fun (name,x) -> (name, sequentialize x))
    ordered_by_file in
    List.iter (fun (_,x) -> merge_ordered x) sequentialized
