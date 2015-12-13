(* This example of proof has been obtained from examples/ex001.lus *)

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

let kind delta_incr p_incr (*max_depth*) =
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
		bmc k;
		kind k;
		loop (k+1)
	in
	loop 0
	
	(*Kind_solver.assume ~id:0 (Formula.make_lit Formula.Lt [Term.make_int (Num.Int 0); n]);*)
	
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



(**************************)
(** Begin generated code **)
(**************************)



let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool
let x__6 = declare_symbol "x__6" [ Type.type_int ] Type.type_bool

(*  n1__4(n)  =  (if n=0 then 0 else (n1__4(n-1) + 1))  *)
let def_n1__4 n =
  let n1__4_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.make_int (Num.Int 0))
    (Term.make_arith Term.Plus (Term.make_app n1__4
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      ) (Term.make_int (Num.Int 1)))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app n1__4
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; n1__4_term ]

(*  n2__5(n)  =  (if n=0 then 1 else (n2__5(n-1) + 1))  *)
let def_n2__5 n =
  let n2__5_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.make_int (Num.Int 1))
    (Term.make_arith Term.Plus (Term.make_app n2__5
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      ) (Term.make_int (Num.Int 1)))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; n2__5_term ]

(*  ok__3(n)  =  aux__8(n)  *)
let def_ok__3 n =
  let ok__3_term = Term.make_app aux__8
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; ok__3_term ]

(*  (aux__8(n)  ==>  ((n1__4(n) + 1) = n2__5(n)))  &&  (((n1__4(n) + 1) = n2__5(n))  ==>  aux__8(n))  *)
let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let aux__8_formula = Formula.make_lit Formula.Eq [ Term.make_arith Term.Plus (Term.make_app n1__4
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ) (Term.make_int (Num.Int 1)); Term.make_app n2__5
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
     ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]



let delta_incr n = Formula.make Formula.And [ def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__8 n ]

let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]

let () = kind delta_incr p_incr
