open Ident
open Asttypes
open Aez_ast

let spf = Format.sprintf

let str_ident ident = spf "%s__%i" ident.name ident.id

let str_constant = function
  | Cbool b -> spf "%b" b
  | Cint n -> spf "%i" n
  | Creal x -> spf "%f" x

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

let rec str_term = function
  | T_cst c -> str_constant c
  | T_op (op, t1, t2) ->
    spf "(%s %s %s)" (str_term t1) (str_term_operator op) (str_term t2)
  | T_ite (f, t1, t2) ->
    (*spf "ite(%s, %s, %s)" (str_formula f) (str_term t1) (str_term t2)*)
	spf "(if %s then %s else %s)" (str_formula f) (str_term t1) (str_term t2)
  | T_app (id, k) -> 
    if k = 0 then spf "%s(n)" (str_ident id)
	else spf "%s(n-%i)" (str_ident id) k
  | T_formula _ | T_tuple _ | T_app_node _ -> assert false
  
and str_formula = function
  | F_term t -> str_term t
  | F_cmp (cmp, t1, t2) -> 
    spf "(%s %s %s)" (str_term t1) (str_comparison cmp) (str_term t2)
  | F_time_eq k -> spf "n=%i" k
  | F_lco (lco, [f1; f2]) -> 
    spf "(%s %s %s)" (str_formula f1) (str_logic_connector lco) (str_formula f2)
  | F_lco (LC_not, [f]) -> spf "not (%s)" (str_formula f)
  | F_lco (lco, f::fs) ->
    spf "(%s) %s %s" (str_formula f) (str_logic_connector lco) (str_formula (F_lco (lco, fs)))
  | F_lco _ -> assert false
  (*| F_lco (lco, []) -> spf "%s([])" (str_logic_connector lco)
  | F_lco (lco, [f]) -> spf "%s(%s)" (str_logic_connector lco) (str_formula f)*)

let str_stream_declaration decl = 
  let s_id = str_ident decl.sd_ident in
  match decl.sd_body with
  | SB_term t -> spf "%s  =  %s" s_id (str_term t)
  | SB_formula f ->
    let s_f = str_formula f in
	spf "(%s  ==>  %s)  &&  (%s  ==>  %s)" s_id s_f s_f s_id


let main decls out_id =
  Format.printf "Boolean output: %s@." (str_ident out_id);
  List.iter (fun decl -> Format.printf "  %s@." (str_stream_declaration decl)) decls;
  Format.printf "@."
