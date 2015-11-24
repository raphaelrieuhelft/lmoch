open Aez
open Smt

module BMC_Solver = Smt.Make(struct end)
module Kind_Solver = Smt.Make(struct end)

exception FalseProperty
exception TrueProperty

let declare_symbol name t_in t_out =
	let x = Hstring.make name in (* creation d’un symbole *)
	Symbol.declare x t_in t_out; (* declaration de son type *)
	x

let kind delta_incr p_incr =
	let k = ref 0 in
	let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
	let n_plus_k = ref n in
	let f_base = p_incr (Term.make_int (Num.Int 0)) in
	BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int 0)));
	BMC_solver.check()
	Kind_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n]);
	Kind_solver.assume ~id:0 (delta_incr !n_plus_k);
	Kind_solver.assume ~id:0 (p_incr !n_plus_k);
	Kind_solver.check();
	try (while true do
		incr k;
		n_plus_k := Term.make_arith Term.plus !n_plus_k (Term.make_int (Num.Int 0));
		f_base := Formula.make Formula.And [!f_base; p_incr !k];
		BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int !k)));
		if not (BMC_solver.entails ~id:0 !f_base;) then raise FalseProperty
		else begin
			Kind_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int !k); n] 
			Kind_solver.assume ~id:0 (delta_incr !n_plus_k)
			Kind_solver.check();
			let p_next = p_incr !n_plus_k in
			if Kind_solver.entails ~id:0 p_next then raise TrueProperty
			else Kind_solver.assume ~id:0 p_next
		end
		done
	)
	with TrueProperty -> Format.printf "TRUE PROPERTY" | FalseProperty -> Format.printf "FALSE PROPERTY"