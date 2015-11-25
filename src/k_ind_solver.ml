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
	let k_term = ref (Term.make_int (Num.Int 0)) in
	let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
	let n_plus_k = ref n in
	let f_base = ref (p_incr (Term.make_int (Num.Int 0))) in
	BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int 0)));
	BMC_solver.check();
	Kind_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n]);
	Kind_solver.assume ~id:0 (delta_incr !n_plus_k);
	Kind_solver.assume ~id:0 (p_incr !n_plus_k);
	Kind_solver.check();
	try (while true do
		incr k;
		k_term := Term.make_arith Term.Plus !k_term (Term.make_int (Num.Int 1));
		n_plus_k := Term.make_arith Term.Plus !n_plus_k (Term.make_int (Num.Int 1));
		f_base := Formula.make Formula.And [!f_base; p_incr !k_term];
		BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int !k)));
		if not (BMC_solver.entails ~id:0 !f_base;) then raise (FalseProperty !k)
		else begin
			Kind_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int !k); n]);
			Kind_solver.assume ~id:0 (delta_incr !n_plus_k);
			Kind_solver.check();
			let p_next = p_incr !n_plus_k in
			if Kind_solver.entails ~id:0 p_next then raise (TrueProperty !k)
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










