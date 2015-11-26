/**************************************/
/* AEZ formulas                       */
/**************************************/
Output to check: ok__6
  cpt__7(n)  =  incr_cpt__11(n)
  ok__6(n)  =  (if n=0 then true else aux__10(n))
  (aux__10(n)  ==>  (cpt__7(n-1) =< cpt__7(n)))  &&  ((cpt__7(n-1) =< cpt__7(n))  ==>  aux__10(n))
  incr_tic__12(n)  =  x__8(n)
  incr_cpt__11(n)  =  ((if n=0 then 0 else incr_cpt__11(n-1)) + (if incr_tic__12(n) then 1 else 0))

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

Don't know
