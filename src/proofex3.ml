/**************************************/
/* AEZ formulas                       */
/**************************************/
Boolean output: OK__3
  n1__4  =  (if n=0 then 0 else (n1__4(n-1) + 1))
  n2__5  =  (if n=0 then 0 else (if n=1 then 0 else (n1__4(n-2) + 2)))
  b1__6  =  (if n=0 then false else true)
  b2__7  =  (if n=0 then false else b1__6(n-1))
  OK__3  =  (if (b1__6(n) && b2__7(n)) then aux__10(n) else true)
  (aux__10  ==>  (n1__4(n) = n2__5(n)))  &&  ((n1__4(n) = n2__5(n))  ==>  aux__10)

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

Don't know
