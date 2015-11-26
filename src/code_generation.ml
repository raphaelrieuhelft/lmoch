open Asttypes
open Aez_ast
open Format

let str_base_type = function
  | Tbool -> "Type.type_bool"
  | Tint -> "Type.type_int"
  | Treal -> "Type.type_float"

let op_string = function 
	|TO_plus -> "Term.Plus"
	|TO_minus -> "Term.Minus"
	|TO_times -> "Term.Mult"
	|TO_div -> "Term.Div"
	|TO_mod -> "Term.Modulo"
 
let comp_string = function
	|Cmp_eq -> "Formula.Eq"
	|Cmp_neq -> "Formula.Neq"
	|Cmp_lt -> "Formula.Lt"
	|Cmp_leq -> "Formula.Le"
	
let lco_string = function
	|LC_and -> "Formula.And"
	|LC_or -> "Formula.Or"
	|LC_impl -> "Formula.Imp"
	|LC_not -> "Formula.Not"

 
let pp_ident = Ident.print

let term_make_int ff n = fprintf ff "Term.make_int (Num.Int %i)" n

let term_make_real ff x = failwith "can't do real numbers yet"

let term_make_cst ff = function 
	|Cint n -> term_make_int ff n
	|Creal x -> term_make_real ff x
	|Cbool true -> fprintf ff "Term.t_true"
	|Cbool false -> fprintf ff "Term.t_false"
	
let rec pp_term ff = function
	|T_cst c -> term_make_cst ff c
	|T_op (op, t1, t2) -> term_make_arith ff (op, t1, t2)
	|T_ite (f, t1, t2) -> term_make_ite ff (f, t1, t2)
	|T_app (id, k) -> term_make_app_k ff (id, k)
	|_-> assert false (*other cases are eliminated in compile_to_aez*)


and term_make_arith ff (op, t1, t2) = fprintf ff "Term.make_arith %s (%a) (%a)" (op_string op) pp_term t1 pp_term t2

and term_make_ite ff (f, t1, t2) = fprintf ff "Term.make_ite@.  (%a)@.  (%a)@.  (%a)" pp_formula f pp_term t1 pp_term t2

and term_make_app_k ff (id, k) = fprintf ff "Term.make_app %a@.  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int %i)) ]" pp_ident id k

and pp_formula ff = function
	|F_term t -> pp_formula ff (F_cmp (Cmp_eq, t, T_cst(Cbool true)))
	|F_cmp (comp, t1, t2) -> formula_make_lit ff (comp, t1, t2)
	|F_time_eq k -> formula_time_eq ff k
	|F_lco (lc, fl) -> formula_make_lco ff (lc, fl)
	
and formula_make_lit ff (comp, t1, t2) = fprintf ff "Formula.make_lit %s [ %a; %a ]" (comp_string comp) pp_term t1 pp_term t2

and formula_time_eq ff k = fprintf ff "Formula.make_lit Formula.Eq [ n; %a ]" term_make_int k

and formula_make_lco ff = function
	|LC_not, [f] -> fprintf ff "Formula.make Formula.Not [ %a ]" pp_formula f
	|lc, [f1; f2] -> fprintf ff "Formula.make %s [ %a; %a ]" (lco_string lc) pp_formula f1 pp_formula f2
	|_-> assert false

let generate_declare_symbol ff decl =
  fprintf ff "let %a = declare_symbol \"%a\" [ Type.type_int ] %s@." pp_ident decl.sd_ident pp_ident decl.sd_ident (str_base_type decl.sd_type)

let generate_declare_symbols ff =
  List.iter (generate_declare_symbol ff)

let generate_stream_decl ff sd =
  fprintf ff "let def_%a n =@." pp_ident sd.sd_ident;
  begin 
  match sd.sd_body with
	|SB_term t -> begin 
		fprintf ff "  let %a_term = %a@.  in@." pp_ident sd.sd_ident pp_term t;
		fprintf ff "  Formula.make_lit Formula.Eq [ %a; %a_term ]@." pp_term (T_app(sd.sd_ident, 0)) pp_ident sd.sd_ident
		end
	|SB_formula f -> begin
		fprintf ff "  let %a_n = %a@.  in@." pp_ident sd.sd_ident pp_formula (F_term (T_app (sd.sd_ident, 0)));
		fprintf ff "  let %a_formula = %a@.  in@." pp_ident sd.sd_ident pp_formula f;
		fprintf ff "  Formula.make Formula.And [@.";
		fprintf ff "    Formula.make Formula.Imp [ %a_n; %a_formula ];@." pp_ident sd.sd_ident pp_ident sd.sd_ident;
		fprintf ff "    Formula.make Formula.Imp [ %a_formula; %a_n ]@." pp_ident sd.sd_ident pp_ident sd.sd_ident;
		fprintf ff "   ]@."
	end
  ;
  fprintf ff "@.@."
  end

  
let generate_stream_decls ff decls = List.iter (generate_stream_decl ff) decls
 
let pp_def_names ff decls = 
  let rec aux = function
  |[]-> ()
  |[sd] -> fprintf ff "def_%a n" pp_ident sd.sd_ident
  |sd::t-> fprintf ff "def_%a n; " pp_ident sd.sd_ident; aux t
  in
  aux decls
 
let main decls out_id =
  let ff = std_formatter in
  generate_declare_symbols ff decls;
  generate_stream_decls ff decls;
  fprintf ff "let delta_incr n = Formula.make Formula.And [ %a ]@." pp_def_names decls;
  fprintf ff "let p_incr n = %a@." pp_formula (F_term (T_app (out_id, 0)));
  fprintf ff "let main () = kind delta_incr p_incr@."; 
  fprintf ff "@."