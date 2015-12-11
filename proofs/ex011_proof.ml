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



(**************************)
(** Begin generated code **)
(**************************)



let b__6 = declare_symbol "b__6" [ Type.type_int ] Type.type_bool
let n1__4 = declare_symbol "n1__4" [ Type.type_int ] Type.type_int
let n2__5 = declare_symbol "n2__5" [ Type.type_int ] Type.type_int
let ok__3 = declare_symbol "ok__3" [ Type.type_int ] Type.type_bool
let aux__8 = declare_symbol "aux__8" [ Type.type_int ] Type.type_bool

(*  b__6(n)  =  (if n=0 then false else true)  *)
let def_b__6 n =
  let b__6_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.t_false)
    (Term.t_true)
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app b__6
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; b__6_term ]

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

(*  n2__5(n)  =  (if n=0 then 1 else (if n=1 then 1 else (n2__5(n-1) + n2__5(n-2))))  *)
let def_n2__5 n =
  let n2__5_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.make_int (Num.Int 1))
    (Term.make_ite
      (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 1) ])
      (Term.make_int (Num.Int 1))
      (Term.make_arith Term.Plus (Term.make_app n2__5
        [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
        ) (Term.make_app n2__5
        [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 2)) ]
        ))
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app n2__5
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; n2__5_term ]

(*  ok__3(n)  =  (if b__6(n) then aux__8(n) else true)  *)
let def_ok__3 n =
  let ok__3_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ Term.make_app b__6
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ])
    (Term.make_app aux__8
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    (Term.t_true)
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__3
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; ok__3_term ]

(*  (aux__8(n)  ==>  (n1__4(n) = n2__5(n)))  &&  ((n1__4(n) = n2__5(n))  ==>  aux__8(n))  *)
let def_aux__8 n =
  let aux__8_n = Formula.make_lit Formula.Eq [ Term.make_app aux__8
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let aux__8_formula = Formula.make_lit Formula.Eq [ Term.make_app n1__4
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.make_app n2__5
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
     ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__8_n; aux__8_formula ];
    Formula.make Formula.Imp [ aux__8_formula; aux__8_n ]
   ]



let delta_incr n = Formula.make Formula.And [ def_b__6 n; def_n1__4 n; def_n2__5 n; def_ok__3 n; def_aux__8 n ]

let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__3
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]

let () = kind delta_incr p_incr
