		
(**********************************)
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