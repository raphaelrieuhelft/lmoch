open Asttypes
open Aez_ast

let fprintf = Format.fprintf



let str_term_operator = function
  | TO_plus -> "+"
  | TO_minus -> "-"
  | TO_times -> "*"
  | TO_div -> "/"
  | TO_mod -> "mod"

let str_comparison = function
  | Cmp_eq -> "="
  | Cmp_neq -> "=/="
  | Cmp_lt -> "<"
  | Cmp_leq -> "=<"

let str_logic_connector = function
  | LC_and -> "&&"
  | LC_or -> "||"
  | LC_impl -> "==>"
  | LC_not -> "not"

let pp_constant ff = function
  | Cbool b -> fprintf ff "%b" b
  | Cint n -> fprintf ff "%i" n
  | Creal x -> fprintf ff "%f" x

let rec pp_term ff = function
  | T_cst c -> pp_constant ff c
  | T_op (op, t1, t2) ->
    fprintf ff "(%a %s %a)" pp_term t1 (str_term_operator op) pp_term t2
  | T_ite (f, t1, t2) ->
	fprintf ff "(if %a then %a else %a)" pp_formula f pp_term t1 pp_term t2
  | T_app (id, k) -> 
    if k = 0 then fprintf ff "%a(n)" Ident.print id
	else fprintf ff "%a(n-%i)" Ident.print id k
  | T_formula _ | T_tuple _ | T_app_node _ -> assert false
  
and pp_formula ff = function
  | F_term t -> pp_term ff t
  | F_cmp (cmp, t1, t2) -> 
    fprintf ff "(%a %s %a)" pp_term t1 (str_comparison cmp) pp_term t2
  | F_time_eq k -> fprintf ff "n=%i" k
  | F_lco (lco, [f1; f2]) -> 
    fprintf ff "(%a %s %a)" pp_formula f1 (str_logic_connector lco) pp_formula f2
  | F_lco (LC_not, [f]) -> fprintf ff "not (%a)" pp_formula f
  | F_lco (LC_and, fs) ->
    let rec pp_fs ff = function
	  | [] -> fprintf ff ""
	  | f::fs -> fprintf ff "%a; %a" pp_formula f pp_fs fs
	in
    fprintf ff "&&list [ %a ]" pp_fs fs
  | F_lco _ -> assert false
  (*| F_lco (lco, []) -> fprintf ff "%s([])" (str_logic_connector lco)
  | F_lco (lco, [f]) -> fprintf ff "%s(%s)" (str_logic_connector lco) (str_formula f)*)

let pp_stream_declaration ff decl = 
  let pp_id ff () = Ident.print ff decl.sd_ident in
  match decl.sd_body with
    | SB_term t -> fprintf ff "%a(n)  =  %a" pp_id () pp_term t
    | SB_formula f ->
      let pp_f ff () = pp_formula ff f in
	  fprintf ff "(%a(n)  ==>  %a)  &&  (%a  ==>  %a(n))" pp_id () pp_f () pp_f () pp_id ()


let str_base_type = function
  | Tbool -> "bool"
  | Tint -> "int"
  | Treal -> "float"
let pp_input_tvars ff input_tvars =
  Format.fprintf ff "Inputs:";
  List.iter (fun (id, bty) -> Format.fprintf ff " %a: %s;" Ident.print id (str_base_type bty)) input_tvars;
  Format.fprintf ff "@."

let main decls input_tvars out_id =
  let ff = Format.std_formatter in
  Format.fprintf ff "Output to check: %a@." Ident.print out_id;
  pp_input_tvars ff input_tvars;
  List.iter (fun decl -> fprintf ff "  %a@." pp_stream_declaration decl) decls;
  Format.fprintf ff "@."
