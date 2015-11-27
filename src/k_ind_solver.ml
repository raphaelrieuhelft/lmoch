open Aez
open Smt

module BMC_solver = Smt.Make(struct end)
module Kind_solver = Smt.Make(struct end)

exception FalseProperty of int
exception TrueProperty of int

let declare_symbol name t_in t_out =
	let x = Hstring.make name in (* creation d’un symbole *)
	Symbol.declare x t_in t_out; (* declaration de son type *)
	x

let kind delta_incr p_incr =
	let k = ref 0 in
	let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
	let n_plus_k = ref n in
	let f_base = ref (p_incr (Term.make_int (Num.Int 0))) in
	BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int 0)));
	BMC_solver.check();
	Kind_solver.assume ~id:0 (Formula.make_lit Formula.Lt [Term.make_int (Num.Int 0); n]);
	Kind_solver.assume ~id:0 (delta_incr !n_plus_k);
	Kind_solver.assume ~id:0 (p_incr !n_plus_k);
	Kind_solver.check();
	try (while true do
		incr k;
		n_plus_k := Term.make_arith Term.Plus !n_plus_k (Term.make_int (Num.Int 1));
		f_base := Formula.make Formula.And [!f_base; p_incr (Term.make_int (Num.Int !k))];
		BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int !k)));
		if not (BMC_solver.entails ~id:0 !f_base;) then raise (FalseProperty !k)
		else begin
			(*Formula.print Format.std_formatter (Formula.make Formula.And [(delta_incr !n_plus_k); (Formula.make_lit Formula.Lt [Term.make_int (Num.Int 0); n])]);
			Format.printf "@.";*)
			Kind_solver.assume ~id:0 (delta_incr !n_plus_k);
			Kind_solver.check();
			let p_next = p_incr !n_plus_k in
			if Kind_solver.entails ~id:0 p_next then ((*Formula.print Format.std_formatter p_next;*) raise (TrueProperty !k))
			else Kind_solver.assume ~id:0 p_next
		end
		done
	)
	with 
	  | TrueProperty k -> 
	    Format.printf "TRUE PROPERTY@.";
		Format.printf "Proven with a %i-induction.@." k
	  | FalseProperty k -> 
	    Format.printf "FALSE PROPERTY@.";
		Format.printf "Base case failed for n = %i.@." k
		
(**********************************)


(*ex011.lus*)

let b__6 = declare_symbol "b__6" [ Type.type_int ] Type.type_bool
let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool
let def_b__6 n =
  let b__6_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.t_false)
  (Term.t_true)
  in
  Formula.make_lit Formula.Eq [ Term.make_app b__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; b__6_term ]
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 1))
  (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 1) ])
  (Term.make_int (Num.Int 1))
  (Term.make_arith Term.Plus (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 2)) ])))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ Term.make_app b__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ])
  (Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ])
  (Term.t_true)
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__8_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_b__6 n; def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__8 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr

(*
(*ex010.lus*)

let b__6 = declare_symbol "b__6" [ Type.type_int ] Type.type_bool
let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__9 = declare_symbol "aux__9" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool
let def_b__6 n =
  let b__6_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.t_true)
  (Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ])
  in
  Formula.make_lit Formula.Eq [ Term.make_app b__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; b__6_term ]
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 1) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 2)) ]) (Term.make_int (Num.Int 2))))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ Term.make_app b__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ])
  (Term.make_app aux__9
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ])
  (Term.t_true)
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__9 n =
  let aux__9_n = Formula.make_lit Formula.Eq [ Term.make_app aux__9
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__9_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__9_n; aux__9_formula ];
    Formula.make Formula.Imp [ aux__9_formula; aux__9_n ]
   ]


let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__8_formula = Formula.make Formula.Not [ Formula.make_lit Formula.Eq [ Term.make_app b__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_b__6 n; def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__9 n; def_aux__8 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)

(*
(*ex009.lus*)

let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__7 = declare_symbol "aux__7" [ Type.type_int ] Type.type_bool
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 1) ])
  (Term.make_int (Num.Int 1))
  (Term.make_arith Term.Plus (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 2)) ]) (Term.make_int (Num.Int 2))))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_app aux__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__7 n =
  let aux__7_n = Formula.make_lit Formula.Eq [ Term.make_app aux__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__7_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__7_n; aux__7_formula ];
    Formula.make Formula.Imp [ aux__7_formula; aux__7_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__7 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)


(*
(*ex004.lus*)

let cpt__7 = declare_symbol "cpt__7" [ Type.type_int ] Type.type_int
let ok__6 = declare_symbol "ok__6" [ Type.type_int ] Type.type_bool
let aux__10 = declare_symbol "aux__10" [ Type.type_int ] Type.type_bool
let incr_tic__12 = declare_symbol "incr_tic__12" [ Type.type_int ] Type.type_bool
let incr_cpt__11 = declare_symbol "incr_cpt__11" [ Type.type_int ] Type.type_int
let x__8 = declare_symbol "x__8" [ Type.type_int ] Type.type_bool
let def_cpt__7 n =
  let cpt__7_term = Term.make_app incr_cpt__11
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
  in
  Formula.make_lit Formula.Eq [ Term.make_app cpt__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; cpt__7_term ]
let def_ok__6 n =
  let ok__6_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.t_true)
  (Term.make_app aux__10
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ])
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__6_term ]
let def_aux__10 n =
  let aux__10_n = Formula.make_lit Formula.Eq [ Term.make_app aux__10
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__10_formula = Formula.make_lit Formula.Le [ Term.make_app cpt__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]; Term.make_app cpt__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__10_n; aux__10_formula ];
    Formula.make Formula.Imp [ aux__10_formula; aux__10_n ]
   ]


let def_incr_tic__12 n =
  let incr_tic__12_term = Term.make_app x__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
  in
  Formula.make_lit Formula.Eq [ Term.make_app incr_tic__12
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; incr_tic__12_term ]
let def_incr_cpt__11 n =
  let incr_cpt__11_term = Term.make_arith Term.Plus (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_app incr_cpt__11
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ])) (Term.make_ite
  (Formula.make_lit Formula.Eq [ Term.make_app incr_tic__12
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ])
  (Term.make_int (Num.Int 1))
  (Term.make_int (Num.Int 0)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app incr_cpt__11
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; incr_cpt__11_term ]
let delta_incr n = Formula.make Formula.And [ def_cpt__7 n; def_ok__6 n; def_aux__10 n; def_incr_tic__12 n; def_incr_cpt__11 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)


(*
(*ex003.lus*)

let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let b1__6 = declare_symbol "b1__6" [ Type.type_int ] Type.type_bool
let b2__7 = declare_symbol "b2__7" [ Type.type_int ] Type.type_bool
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__10 = declare_symbol "aux__10" [ Type.type_int ] Type.type_bool
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 1) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 2)) ]) (Term.make_int (Num.Int 2))))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_b1__6 n =
  let b1__6_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.t_false)
  (Term.t_true)
  in
  Formula.make_lit Formula.Eq [ Term.make_app b1__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; b1__6_term ]
let def_b2__7 n =
  let b2__7_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.t_false)
  (Term.make_app b1__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ])
  in
  Formula.make_lit Formula.Eq [ Term.make_app b2__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; b2__7_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_ite
  (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app b1__6
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app b2__7
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ] ])
  (Term.make_app aux__10
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ])
  (Term.t_true)
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__10 n =
  let aux__10_n = Formula.make_lit Formula.Eq [ Term.make_app aux__10
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__10_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__10_n; aux__10_formula ];
    Formula.make Formula.Imp [ aux__10_formula; aux__10_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_n1__4 n; def_n2__5 n; def_b1__6 n; def_b2__7 n; def_ok__3 n; def_aux__10 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)

(*
(*ex002.lus*)

let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 1))
  (Term.make_arith Term.Plus (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1))))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__8_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__8 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)


(*  (*ex001.lus*)
let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool
let def_n1__4 n =
  let n1__4_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 0))
  (Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n1__4_term ]
let def_n2__5 n =
  let n2__5_term = Term.make_ite
  (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
  (Term.make_int (Num.Int 1))
  (Term.make_arith Term.Plus (Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]) (Term.make_int (Num.Int 1)))
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; n2__5_term ]
let def_ok__3 n =
  let ok__3_term = Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; ok__3_term ]
let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
  in
  let aux__8_formula = Formula.make_lit Formula.Eq [ Term.make_arith Term.Plus (Term.make_app n1__4
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]) (Term.make_int (Num.Int 1)); Term.make_app n2__5
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__8 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
  [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]; Term.t_true ]
let main () = kind delta_incr p_incr
*)


(*


let tic = declare_symbol "tic" [ Type.type_int ] Type.type_bool
let ok = declare_symbol "ok" [ Type.type_int ] Type.type_bool
let cpt = declare_symbol "cpt" [ Type.type_int ] Type.type_int
let aux = declare_symbol "aux" [ Type.type_int ] Type.type_bool

let def_cpt n =
(* cpt(n) = ite(n = 0, 0, cpt(n-1)) + ite(tic(n), 1, 0) *)
let ite1 = (* ite(n = 0, 0, cpt(n-1)) *)
Term.make_ite
(Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
(Term.make_int (Num.Int 0))
(Term.make_app cpt
[ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ])
in
let ite2 = (* ite(tic(n), 1, 0) *)
Term.make_ite
(Formula.make_lit Formula.Eq [Term.make_app tic [n]; Term.t_true])
(Term.make_int (Num.Int 1))
(Term.make_int (Num.Int 0))
in
(* cpt(n) = ite1 + ite2 *)
Formula.make_lit Formula.Eq
[ Term.make_app cpt [n] ;
Term.make_arith Term.Plus ite1 ite2 ]
let def_ok n =
(* ok(n) = ite(n = 0, true, aux(n)) *)
Formula.make_lit Formula.Eq
[ Term.make_app ok [n] ;
Term.make_ite
(Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
Term.t_true
(Term.make_app aux [n]) ]
let def_aux n =
let aux_n = (* aux(n) = true *)
Formula.make_lit Formula.Eq [ Term.make_app aux [n]; Term.t_true ]
in
let pre_cpt_le_cpt = (* cpt(n-1) <= cpt(n) *)
Formula.make_lit Formula.Le [ Term.make_app cpt
[ Term.make_arith Term.Minus
n (Term.make_int (Num.Int 1)) ];
Term.make_app cpt [n] ]
in
Formula.make Formula.And
[ Formula.make Formula.Imp [ aux_n; pre_cpt_le_cpt ] ;
Formula.make Formula.Imp [ pre_cpt_le_cpt; aux_n ] ]

let delta_incr n = Formula.make Formula.And [ def_cpt n; def_ok n; def_aux n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok [n]; Term.t_true ]


let main () = kind delta_incr p_incr

*)




