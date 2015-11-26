/**************************************/
/* AEZ formulas                       */
/**************************************/
Boolean output: OK__3
  n1__4  =  (if n=0 then 0 else (n1__4(n-1) + 1))
  n2__5  =  (if n=0 then 1 else (n2__5(n-1) + 1))
  OK__3  =  aux__8(n)
  (aux__8  ==>  ((n1__4(n) + 1) = n2__5(n)))  &&  (((n1__4(n) + 1) = n2__5(n))  ==>  aux__8)

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

Don't know
