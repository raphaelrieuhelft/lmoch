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

let kind delta_incr p_incr max_special_case =
try
  
	let ok i = p_incr (Term.make_int (Num.Int i)) in
    let delta i = delta_incr (Term.make_int (Num.Int i)) in
	let bmc k =
		BMC_solver.assume ~id:0 (delta k);
		if not (BMC_solver.entails ~id:0 (ok k)) then raise (FalseProperty k)
	in
	
	let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
	let kind k =
		let n_plus_k = Term.make_arith Term.Plus n (Term.make_int (Num.Int k)) in
		Kind_solver.assume ~id:0 (delta_incr n_plus_k);
		Kind_solver.check();
		let p_n_plus_k = p_incr n_plus_k in
		if Kind_solver.entails ~id:0 p_n_plus_k then raise (TrueProperty k);
		Kind_solver.assume ~id:0 p_n_plus_k
	in
	
	let rec loop k =
		if k <= max_special_case then (bmc k; loop (k+1))
	in loop 0;
	
	Kind_solver.assume ~id:0 (Formula.make_lit Formula.Lt [Term.make_int (Num.Int max_special_case); n]);
	
	let rec loop k =
		if k > max_special_case then bmc k;
		kind k;
		loop (k+1)
	in
	loop 0
	
with 
	  | TrueProperty k -> 
	    Format.printf "TRUE PROPERTY@.";
		if k > 0 then
			Format.printf "Proved with a %i-induction.@." k
		else
			Format.printf "Proved without the need for induction.@."
	  | FalseProperty k -> 
	    Format.printf "FALSE PROPERTY@.";
		Format.printf "Base case failed for n = %i.@." k



