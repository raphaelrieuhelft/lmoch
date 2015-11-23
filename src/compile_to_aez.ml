open Typed_ast
open Aez_ast


module IdMap = Map.make (struct type t = ident let compare = compare end)

(* ('a -> 'b -> ('c * 'a)) -> 'a -> ('b list) -> (('c list) * 'a) *)
let rec map_fold f a = function
  | [] -> [], a
  | b::bs ->
    let c, a1 = f a b in
	let cs, a2 = map_fold f a1 bs in
	c::cs, a2

let rec list_map3 f l1 l2 l3 = match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (f h1 h2 h3)::(list_map3 t1 t2 t3)
  | _ -> raise Invalid_argument





(* expr to term, including T_formula, T_tuple, T_app_node *)
let rec compile_expr past expr = match expr.texpr_disc with

  | TE_const c -> T_cst c
  
  | TE_ident ident -> T_app (ident, past)
  
  | TE_op (op, exprs) ->
    let terms = List.map (compile_expr past) exprs in
    begin
	  match op with
	    | Op_add | Op_sub | Op_mul | Op_div | Op_mod
		| Op_add_f | Op_sub_f | Op_mul_f | Op_div_f ->
		  let term_op = match op with
            | Op_add | Op_add_f -> TO_plus
			| Op_sub | Op_sub_f -> TO_minus
			| Op_mul | Op_mul_f -> TO_times
			| Op_div | Op_div_f -> TO_div
			| Op_mod -> TO_mod
		  in
		  (match terms with [term1; term2] ->
		    T_op (term_op, term1, term2))
			
		| Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge ->
		  let cmp, exchange = match op with
		    | Op_eq -> Cmp_eq, false
			| Op_neq -> Cmp_neq, false
			| Op_lt -> Cmp_lt, false
			| Op_le -> Cmp_leq, false
			| Op_gt -> Cmp_leq, true
			| Op_ge -> Cmp_lt, true
		  in
		  let formula = match terms with [term1; term2] ->
		    if exchange then F_cmp (cmp, term2, term1) else F_cmp (cmp, term1, term2)
		  in
		  T_formula formula
			
		| Op_and | Op_or | Op_impl | Op_not ->
		  let lco = match op with
		    | Op_and -> LC_and | Op_or -> Lc_or 
			| Op_impl -> LC_impl | Op_not -> LC_not
		  in
		  let formulas = List.map (fun t -> F_term t) terms in
		  T_formula (F_lco (lco, formulas))
		  
		| Op_if -> (match terms with [cond; term1; term2] ->
		  T_ite (F_term cond, term1, term2)
	end
  
  | TE_app (ident, exprs) ->
    let terms = List.map (compile_expr past) exprs in
	T_app_node (ident, past, terms)
  
  | TE_prim (_, [expr]) -> compile_expr past expr
  
  | TE_arrow (expr1, expr2) ->
    let term1 = compile_expr past expr1 in
	let term2 = compile_expr past expr2 in
	T_ite (F_time_eq past, term1, term2)
	
  | TE_pre expr -> compile_expr (incr past) expr
  
  | TE_tuple exprs -> 
    let terms = List.map (compile_expr past) exprs in
	T_tuple terms





	
	
	
	
let rec separate_formulas_in_term aux_decls term = match term with
  | T_cst _ -> term, aux_decls
  | T_op (op, t1, t2) ->
    let t1, aux_decls = separate_formulas_in_term aux_decls t1 in
	let t2, aux_decls = separate_formulas_in_term aux_decls t2 in
	T_op (op, t1, t2), aux_decls
  | T_ite (f, t1, t2) ->
    let f, aux_decls = separate_formulas_in_formula aux_decls f in
	let t1, aux_decls = separate_formulas_in_term aux_decls t1 in
	let t2, aux_decls = separate_formulas_in_term aux_decls t2 in
	T_ite (f, t1, t2), aux_decls
  | T_app (_,_) -> term, aux_decls
  | T_formula f ->
    let f, aux_decls = separate_formulas_in_formula aux_decls f in
    let ident = Ident.make "aux" Ident.Stream in
	let decl = { sd_ident = ident; sd_type = Tbool; sd_body = SB_formula f } in
	TE_app (ident, 0), decl::aux_decls
  | T_tuple ts ->
    let ts, aux_decls = map_fold separate_formulas_in_term aux_decls ts in
	T_tuple ts, aux_decls
  | T_app_node (id, past, ts) ->
    let ts, aux_decls = map_fold separate_formulas_in_term aux_decls ts in
	T_app_node (id, past, ts), aux_decls
  
and separate_formulas_in_formula aux_decls formula = match formula with
  | F_term term -> (match term with
	| T_formula f -> separate_formulas_in_formula aux_decls f
	| _ -> let t, aux_decls = separate_formulas_in_term aux_decls term in
	  F_term t, aux_decls)
  | F_cmp (cmp, t1, t2) ->
    let t1, aux_decls = separate_formulas_in_term aux_decls t1 in
	let t2, aux_decls = separate_formulas_in_term aux_decls t2 in
	F_cmp (cmp, t1, t2), aux_decls
  | F_time_eq _ -> formula, aux_decls
  | F_lco (lco, formulas) ->
    let fs, aux_decls = map_fold separate_formulas_in_formula aux_decls formulas in
	F_lco (lco, fs), aux_decls









type node_call = {
  nc_node: t_node;
  nc_past: int;
  nc_args: term list;
  nc_outs: ident list;
}

let reid node_ident ident = match ident.kind with
  | Stream ->
    Ident.make (node_ident.name ^ "_" ^ ident.name) ident.kind
  | Node -> assert false
  | Prim -> assert false
  
let find_node t_file node_ident =
  try List.find (fun tn -> tn.tn_name = ident) t_file
  with Not_found -> assert false

  
  
  
let separate_tuples t_file tpatt_term_couples aux_decls =

  let make_node_call ident past terms =
    let node = find_node t_file ident in
	let outs = List.map (fun (id,_) -> reid node.tn_name id) node.tn_output in
	{ nc_node = node; nc_past = past; nc_args = terms; nc_outs = outs }
  in
  
  let rec handle_term node_calls term = match term with
    | T_cst _ -> [term], node_calls
	| T_op (op, t1, t2) ->
      let ts1, node_calls = handle_term node_calls t1 in
	  let ts2, node_calls = handle_term node_calls t2 in
	  List.map2 (fun t1 t2 -> T_op (op, t1, t2)) ts1 ts2, aux_decls
	| T_ite (f, t1, t2) ->
	  let f, node_calls = handle_formula node_calls f in
	  let ts1, node_calls = handle_term node_calls t1 in
	  let ts2, node_calls = handle_term node_calls t2 in
	  List.map2 (fun t1 t2 -> T_ite (f, t1, t2)) ts1 ts2, node_calls
	| T_app (_,_) -> [term], node_calls
	| T_formula _ -> assert false
	| T_tuple ts ->
	  let tss, node_calls = map_fold handle_term node_calls ts in
	  List.map (function [t] -> t) tss, node_calls
	| T_app_node (id, past, ts) ->
	  let tss, node_calls = map_fold handle_term node_calls ts in
	  let nc = make_node_call id past (List.map (function [t] -> t) tss) in
	  List.map (fun id -> T_app (id, past)) nc.nc_outs, nc::node_calls
	  
  and handle_formula node_calls formula = match formula with
    | F_term t ->
	  let ts, node_calls = handle_term node_calls t in
	  F_lco (LC_and, List.map (fun t -> F_term t) ts), node_calls
	| F_cmp (cmp, t1, t2) ->
	  let ts1, node_calls = handle_term node_calls t1 in
	  let ts2, node_calls = handle_term node_calls t2 in
	  F_lco (LC_and, List.map2 (fun t1 t2 -> F_cmp (cmp, t1, t2)) ts1 ts2),
	    node_calls
	| F_time_eq _ -> formula, node_calls
	| F_lco (lco, fs) ->
	  let fs, node_calls = map_fold handle_formula node_calls fs in
	  F_lco (lco, fs), node_calls  
  in
  
  let handle_tpatt_term_couple (decls_acc, node_calls) (tpatt, term) =
    let terms, node_calls = handle_term node_calls term in
	let decls = list_map3 (fun ident bty term ->
	  { sd_ident = ident; sd_type = bty; sd_body = SB_term term }
	) tpatt.tpatt_desc tpatt.tpatt_type terms in
	decls@decls_acc, node_calls
  in
  
  let handle_aux_decl (decls_acc, node_calls) decl =
    let formula = match decl.sd_body with SB_formula f -> f | SB_term _ -> assert false in
    let formula, node_calls = handle_formula node_calls formula in
	let decl = { sd_ident = decl.sd_ident; sd_type = decl.sd_type; sd_body = SB_formula formula } in
	decl::decls_acc, node_calls
  in
  
  let decls, node_calls = List.fold_left handle_tpatt_term_couple ([],[]) tpatt_term_couples in
  
  let decls, node_calls = List.fold_left handle_aux_decl (decls, node_calls) aux_decls in
  
  decls, node_calls
  
 

  
let reid_decls node_id init_reidmap decls =
  let reid_ident reidmap ident =
    if IdMap.mem ident reidmap then
	  IdMap.find ident reidmap, reidmap
	else
	  let new_id = reid node_id ident in
	  new_id, IdMap.add ident new_id reidmap
  in

  let rec reid_term reidmap term = match term with
    | T_cst _ -> term, reidmap
    | T_op (op, t1, t2) ->
      let t1, reidmap = reid_term reidmap t1 in
	  let t2, reidmap = reid_term reidmap t2 in
	  T_op (op, t1, t2), reidmap
    | T_ite (f, t1, t2) ->
      let f, reidmap = reid_formula reidmap f in
      let t1, reidmap = reid_term reidmap t1 in
	  let t2, reidmap = reid_term reidmap t2 in
	  T_ite (f, t1, t2), reidmap
    | T_app (ident, past) ->
      let ident, reidmap = reid_ident reidmap ident in
	  T_app (ident, past), reidmap
    | T_formula _ | T_tuple _ | T_app_node _ -> assert false
  and reid_formula reidmap formula = match formula with
    | F_term t ->
	  let t, reidmap = reid_term reidmap t in
	  F_term t, reidmap
	| F_cmp (cmp, t1, t2) ->
	  let t1, reidmap = reid_term reidmap t1 in
	  let t2, reidmap = reid_term reidmap t2 in
	  F_cmp (cmp, t1, t2), reidmap
	| F_time_eq _ -> formula, reidmap
	| F_lco (lco, fs) ->
	  let fs, reidmap = map_fold reid_formula reidmap fs in
	  F_lco (lco, fs), reidmap
  in
  
  let reid_decl reidmap decl =
    let ident, reidmap = reid_ident reidmap decl.sd_ident in
	let body, reidmap = match decl.sd_body with
	  | SB_term t ->
	    let t, reidmap = reid_term reidmap t in
		SB_term t, reidmap
	  | SB_formula f ->
	    let f, reidmap = reid_formula reidmap f in
		SB_formula f, reidmap
    in
	{ sd_ident = ident; sd_type = decl.sd_type; sd_body = body }, reidmap
  in
  
  let decls, reidmap = map_fold reid_decl init_reidmap decls in
  
  decls, reidmap
  

let rec compute_node_call t_file compiled_nodes nc =
  let node_id = nc.nc_node.tn_name in
  let node_decls, compiled_nodes = compile_node t_file computed_node node_id in
  let init_reidmap = List.fold_left2
    (fun reidmap (id1,_) id2 -> IdMap.add id1 id2 reidmap)
	IdMap.empty nc.nc_node.tn_output nc.nc_outs in
  let node_decls, reidmap = reid_decls node_id init_reidmap node_decls in
  let args_decls = List.map2
    (fun (id,bty) term ->
	  let id = try IdMap.find id reidmap with Not_found -> reid node_id id in
	  { sd_ident = id; sd_type = bty; sd_body = SB_term term })
	nc.nc_node.tn_input nc.nc_args in
  args_decls@node_decls, compiled_nodes


  
and compile_equations t_file compiled_nodes equations =

  let tpatt_term_couples1 = List.map (fun eq -> (eq.teq_patt, compile_expr 0 eq.teq_expr)) equations in
  
  let tpatt_term_couples2, aux_decls = map_fold
    (fun aux_decls (tp, term) ->
	  let term, aux_decls = separate_formulas_in_term aux_decls term in
	  (tp, term), aux_decls)
	aux_decls tpatt_term_couples1 in
	
  let own_decls, node_calls = separate_tuples t_file tpatt_term_couples2 aux_decls in
  
  let node_call_decls_list, compiled_nodes = map_fold (compute_node_call t_file) compiled_nodes node_calls in
  
  let decls = List.concat (own_decls::node_call_decls_list) in
  
  decls, compiled_nodes


  
and compile_node t_file compiled_nodes node =
  let node_id = node.tn_name in
  if IdMap.mem node_id compiled_nodes then
	IdMap.find node_id compiled_nodes, compiled_nodes
  else
	let decls, compiled_nodes = compile_equations t_file compiled_nodes node.tn_equs in
	decls, IdMap.add node_id decls compiled_nodes
	
  
  
  
  
let main t_file main_node_id =
  let node = find_node t_file main_node_id in
  let output_id = match node.tn_input with
    | [(id, bty)] when bty = Tbool -> id
	| _ -> assert false
  in
  let decls, _ = compile_node t_file IdMap.empty node in
  decls, output_id




(* questions: 
  tuple in tuple 
  distribute op / conn over tuple
*)

(* examples: 
  cf questions
  call a node in the past -> ?
  input of a node unused 
*)

(* remark: loops if there is a loop in node calls, assume checked by parser when giving ids to nodes *)







