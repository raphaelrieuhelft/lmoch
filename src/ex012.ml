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

let cpt__58 = declare_symbol "cpt__58" [ Type.type_int ] Type.type_int
let x3__62 = declare_symbol "x3__62" [ Type.type_int ] Type.type_bool
let x2__61 = declare_symbol "x2__61" [ Type.type_int ] Type.type_bool
let x1__60 = declare_symbol "x1__60" [ Type.type_int ] Type.type_bool
let x0__59 = declare_symbol "x0__59" [ Type.type_int ] Type.type_bool
let ok__57 = declare_symbol "ok__57" [ Type.type_int ] Type.type_bool
let aux__64 = declare_symbol "aux__64" [ Type.type_int ] Type.type_bool
let int_of_4bits_x0__89 = declare_symbol "int_of_4bits_x0__89" [ Type.type_int ] Type.type_bool
let int_of_4bits_x1__87 = declare_symbol "int_of_4bits_x1__87" [ Type.type_int ] Type.type_bool
let int_of_4bits_x2__85 = declare_symbol "int_of_4bits_x2__85" [ Type.type_int ] Type.type_bool
let int_of_4bits_x3__83 = declare_symbol "int_of_4bits_x3__83" [ Type.type_int ] Type.type_bool
let int_of_4bits_out__69 = declare_symbol "int_of_4bits_out__69" [ Type.type_int ] Type.type_int
let int_of_4bits_int_of_bit_x__82 = declare_symbol "int_of_4bits_int_of_bit_x__82" [ Type.type_int ] Type.type_bool
let int_of_4bits_int_of_bit_out__81 = declare_symbol "int_of_4bits_int_of_bit_out__81" [ Type.type_int ] Type.type_int
let int_of_4bits_int_of_bit_x__84 = declare_symbol "int_of_4bits_int_of_bit_x__84" [ Type.type_int ] Type.type_bool
let int_of_4bits_int_of_bit_out__80 = declare_symbol "int_of_4bits_int_of_bit_out__80" [ Type.type_int ] Type.type_int
let int_of_4bits_int_of_bit_x__86 = declare_symbol "int_of_4bits_int_of_bit_x__86" [ Type.type_int ] Type.type_bool
let int_of_4bits_int_of_bit_out__79 = declare_symbol "int_of_4bits_int_of_bit_out__79" [ Type.type_int ] Type.type_int
let int_of_4bits_int_of_bit_x__88 = declare_symbol "int_of_4bits_int_of_bit_x__88" [ Type.type_int ] Type.type_bool
let int_of_4bits_int_of_bit_out__78 = declare_symbol "int_of_4bits_int_of_bit_out__78" [ Type.type_int ] Type.type_int
let inc4_x0__353 = declare_symbol "inc4_x0__353" [ Type.type_int ] Type.type_bool
let inc4_x1__355 = declare_symbol "inc4_x1__355" [ Type.type_int ] Type.type_bool
let inc4_x2__357 = declare_symbol "inc4_x2__357" [ Type.type_int ] Type.type_bool
let inc4_x3__359 = declare_symbol "inc4_x3__359" [ Type.type_int ] Type.type_bool
let inc4_out3__68 = declare_symbol "inc4_out3__68" [ Type.type_int ] Type.type_bool
let inc4_out2__67 = declare_symbol "inc4_out2__67" [ Type.type_int ] Type.type_bool
let inc4_out1__66 = declare_symbol "inc4_out1__66" [ Type.type_int ] Type.type_bool
let inc4_out0__65 = declare_symbol "inc4_out0__65" [ Type.type_int ] Type.type_bool
let inc4_add4_a0__352 = declare_symbol "inc4_add4_a0__352" [ Type.type_int ] Type.type_bool
let inc4_add4_a1__354 = declare_symbol "inc4_add4_a1__354" [ Type.type_int ] Type.type_bool
let inc4_add4_a2__356 = declare_symbol "inc4_add4_a2__356" [ Type.type_int ] Type.type_bool
let inc4_add4_a3__358 = declare_symbol "inc4_add4_a3__358" [ Type.type_int ] Type.type_bool
let inc4_add4_b0__360 = declare_symbol "inc4_add4_b0__360" [ Type.type_int ] Type.type_bool
let inc4_add4_b1__361 = declare_symbol "inc4_add4_b1__361" [ Type.type_int ] Type.type_bool
let inc4_add4_b2__362 = declare_symbol "inc4_add4_b2__362" [ Type.type_int ] Type.type_bool
let inc4_add4_b3__363 = declare_symbol "inc4_add4_b3__363" [ Type.type_int ] Type.type_bool
let inc4_add4_c__364 = declare_symbol "inc4_add4_c__364" [ Type.type_int ] Type.type_bool
let inc4_add4_c0__365 = declare_symbol "inc4_add4_c0__365" [ Type.type_int ] Type.type_bool
let inc4_add4_out0__351 = declare_symbol "inc4_add4_out0__351" [ Type.type_int ] Type.type_bool
let inc4_add4_c1__368 = declare_symbol "inc4_add4_c1__368" [ Type.type_int ] Type.type_bool
let inc4_add4_out1__350 = declare_symbol "inc4_add4_out1__350" [ Type.type_int ] Type.type_bool
let inc4_add4_c2__371 = declare_symbol "inc4_add4_c2__371" [ Type.type_int ] Type.type_bool
let inc4_add4_out2__349 = declare_symbol "inc4_add4_out2__349" [ Type.type_int ] Type.type_bool
let inc4_add4_c3__374 = declare_symbol "inc4_add4_c3__374" [ Type.type_int ] Type.type_bool
let inc4_add4_out3__348 = declare_symbol "inc4_add4_out3__348" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_a__377 = declare_symbol "inc4_add4_fulladder_a__377" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_b__378 = declare_symbol "inc4_add4_fulladder_b__378" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c__379 = declare_symbol "inc4_add4_fulladder_c__379" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c1__380 = declare_symbol "inc4_add4_fulladder_c1__380" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_s1__382 = declare_symbol "inc4_add4_fulladder_s1__382" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c2__384 = declare_symbol "inc4_add4_fulladder_c2__384" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_sum__376 = declare_symbol "inc4_add4_fulladder_sum__376" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_carry__375 = declare_symbol "inc4_add4_fulladder_carry__375" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_aux__387 = declare_symbol "inc4_add4_fulladder_aux__387" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__388 = declare_symbol "inc4_add4_fulladder_halfadder_a__388" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__389 = declare_symbol "inc4_add4_fulladder_halfadder_b__389" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__386 = declare_symbol "inc4_add4_fulladder_halfadder_sum__386" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__385 = declare_symbol "inc4_add4_fulladder_halfadder_carry__385" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__391 = declare_symbol "inc4_add4_fulladder_halfadder_aux__391" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__392 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__392" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__393 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__393" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__390 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__390" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__394 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__394" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__395 = declare_symbol "inc4_add4_fulladder_halfadder_a__395" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__396 = declare_symbol "inc4_add4_fulladder_halfadder_b__396" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__383 = declare_symbol "inc4_add4_fulladder_halfadder_sum__383" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__381 = declare_symbol "inc4_add4_fulladder_halfadder_carry__381" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__398 = declare_symbol "inc4_add4_fulladder_halfadder_aux__398" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__399 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__399" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__400 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__400" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__397 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__397" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__401 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__401" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_a__402 = declare_symbol "inc4_add4_fulladder_a__402" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_b__403 = declare_symbol "inc4_add4_fulladder_b__403" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c__404 = declare_symbol "inc4_add4_fulladder_c__404" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c1__405 = declare_symbol "inc4_add4_fulladder_c1__405" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_s1__407 = declare_symbol "inc4_add4_fulladder_s1__407" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c2__409 = declare_symbol "inc4_add4_fulladder_c2__409" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_sum__373 = declare_symbol "inc4_add4_fulladder_sum__373" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_carry__372 = declare_symbol "inc4_add4_fulladder_carry__372" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_aux__412 = declare_symbol "inc4_add4_fulladder_aux__412" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__413 = declare_symbol "inc4_add4_fulladder_halfadder_a__413" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__414 = declare_symbol "inc4_add4_fulladder_halfadder_b__414" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__411 = declare_symbol "inc4_add4_fulladder_halfadder_sum__411" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__410 = declare_symbol "inc4_add4_fulladder_halfadder_carry__410" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__416 = declare_symbol "inc4_add4_fulladder_halfadder_aux__416" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__417 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__417" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__418 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__418" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__415 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__415" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__419 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__419" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__420 = declare_symbol "inc4_add4_fulladder_halfadder_a__420" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__421 = declare_symbol "inc4_add4_fulladder_halfadder_b__421" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__408 = declare_symbol "inc4_add4_fulladder_halfadder_sum__408" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__406 = declare_symbol "inc4_add4_fulladder_halfadder_carry__406" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__423 = declare_symbol "inc4_add4_fulladder_halfadder_aux__423" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__424 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__424" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__425 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__425" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__422 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__422" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__426 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__426" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_a__427 = declare_symbol "inc4_add4_fulladder_a__427" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_b__428 = declare_symbol "inc4_add4_fulladder_b__428" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c__429 = declare_symbol "inc4_add4_fulladder_c__429" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c1__430 = declare_symbol "inc4_add4_fulladder_c1__430" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_s1__432 = declare_symbol "inc4_add4_fulladder_s1__432" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c2__434 = declare_symbol "inc4_add4_fulladder_c2__434" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_sum__370 = declare_symbol "inc4_add4_fulladder_sum__370" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_carry__369 = declare_symbol "inc4_add4_fulladder_carry__369" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_aux__437 = declare_symbol "inc4_add4_fulladder_aux__437" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__438 = declare_symbol "inc4_add4_fulladder_halfadder_a__438" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__439 = declare_symbol "inc4_add4_fulladder_halfadder_b__439" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__436 = declare_symbol "inc4_add4_fulladder_halfadder_sum__436" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__435 = declare_symbol "inc4_add4_fulladder_halfadder_carry__435" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__441 = declare_symbol "inc4_add4_fulladder_halfadder_aux__441" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__442 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__442" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__443 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__443" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__440 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__440" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__444 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__444" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__445 = declare_symbol "inc4_add4_fulladder_halfadder_a__445" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__446 = declare_symbol "inc4_add4_fulladder_halfadder_b__446" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__433 = declare_symbol "inc4_add4_fulladder_halfadder_sum__433" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__431 = declare_symbol "inc4_add4_fulladder_halfadder_carry__431" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__448 = declare_symbol "inc4_add4_fulladder_halfadder_aux__448" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__449 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__449" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__450 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__450" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__447 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__447" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__451 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__451" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_a__452 = declare_symbol "inc4_add4_fulladder_a__452" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_b__453 = declare_symbol "inc4_add4_fulladder_b__453" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c__454 = declare_symbol "inc4_add4_fulladder_c__454" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c1__455 = declare_symbol "inc4_add4_fulladder_c1__455" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_s1__457 = declare_symbol "inc4_add4_fulladder_s1__457" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_c2__459 = declare_symbol "inc4_add4_fulladder_c2__459" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_sum__367 = declare_symbol "inc4_add4_fulladder_sum__367" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_carry__366 = declare_symbol "inc4_add4_fulladder_carry__366" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_aux__462 = declare_symbol "inc4_add4_fulladder_aux__462" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__463 = declare_symbol "inc4_add4_fulladder_halfadder_a__463" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__464 = declare_symbol "inc4_add4_fulladder_halfadder_b__464" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__461 = declare_symbol "inc4_add4_fulladder_halfadder_sum__461" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__460 = declare_symbol "inc4_add4_fulladder_halfadder_carry__460" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__466 = declare_symbol "inc4_add4_fulladder_halfadder_aux__466" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__467 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__467" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__468 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__468" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__465 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__465" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__469 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__469" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_a__470 = declare_symbol "inc4_add4_fulladder_halfadder_a__470" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_b__471 = declare_symbol "inc4_add4_fulladder_halfadder_b__471" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_sum__458 = declare_symbol "inc4_add4_fulladder_halfadder_sum__458" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_carry__456 = declare_symbol "inc4_add4_fulladder_halfadder_carry__456" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_aux__473 = declare_symbol "inc4_add4_fulladder_halfadder_aux__473" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_a__474 = declare_symbol "inc4_add4_fulladder_halfadder_xor_a__474" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_b__475 = declare_symbol "inc4_add4_fulladder_halfadder_xor_b__475" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_out__472 = declare_symbol "inc4_add4_fulladder_halfadder_xor_out__472" [ Type.type_int ] Type.type_bool
let inc4_add4_fulladder_halfadder_xor_aux__476 = declare_symbol "inc4_add4_fulladder_halfadder_xor_aux__476" [ Type.type_int ] Type.type_bool
let def_cpt__58 n =
  (*  cpt__58(n)  =  (if n=0 then 0 else (cpt__58(n-1) + 1))  *)
  let cpt__58_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.make_int (Num.Int 0))
    (Term.make_arith Term.Plus (Term.make_app cpt__58
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      ) (Term.make_int (Num.Int 1)))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app cpt__58
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; cpt__58_term ]
let def_x3__62 n =
  (*  x3__62(n)  =  (if n=0 then false else inc4_out3__68(n-1))  *)
  let x3__62_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.t_false)
    (Term.make_app inc4_out3__68
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app x3__62
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; x3__62_term ]
let def_x2__61 n =
  (*  x2__61(n)  =  (if n=0 then false else inc4_out2__67(n-1))  *)
  let x2__61_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.t_false)
    (Term.make_app inc4_out2__67
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app x2__61
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; x2__61_term ]
let def_x1__60 n =
  (*  x1__60(n)  =  (if n=0 then false else inc4_out1__66(n-1))  *)
  let x1__60_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.t_false)
    (Term.make_app inc4_out1__66
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app x1__60
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; x1__60_term ]
let def_x0__59 n =
  (*  x0__59(n)  =  (if n=0 then false else inc4_out0__65(n-1))  *)
  let x0__59_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
    (Term.t_false)
    (Term.make_app inc4_out0__65
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app x0__59
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; x0__59_term ]
let def_ok__57 n =
  (*  ok__57(n)  =  aux__64(n)  *)
  let ok__57_term = Term.make_app aux__64
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app ok__57
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; ok__57_term ]
let def_aux__64 n =
  (*  (aux__64(n)  ==>  (cpt__58(n) = int_of_4bits_out__69(n)))  &&  ((cpt__58(n) = int_of_4bits_out__69(n))  ==>  aux__64(n))  *)
  let aux__64_n = Formula.make_lit Formula.Eq [ Term.make_app aux__64
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let aux__64_formula = Formula.make_lit Formula.Eq [ Term.make_app cpt__58
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.make_app int_of_4bits_out__69
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
     ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ aux__64_n; aux__64_formula ];
    Formula.make Formula.Imp [ aux__64_formula; aux__64_n ]
   ]


let def_int_of_4bits_x0__89 n =
  (*  int_of_4bits_x0__89(n)  =  x0__59(n)  *)
  let int_of_4bits_x0__89_term = Term.make_app x0__59
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_x0__89
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_x0__89_term ]
let def_int_of_4bits_x1__87 n =
  (*  int_of_4bits_x1__87(n)  =  x1__60(n)  *)
  let int_of_4bits_x1__87_term = Term.make_app x1__60
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_x1__87
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_x1__87_term ]
let def_int_of_4bits_x2__85 n =
  (*  int_of_4bits_x2__85(n)  =  x2__61(n)  *)
  let int_of_4bits_x2__85_term = Term.make_app x2__61
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_x2__85
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_x2__85_term ]
let def_int_of_4bits_x3__83 n =
  (*  int_of_4bits_x3__83(n)  =  x3__62(n)  *)
  let int_of_4bits_x3__83_term = Term.make_app x3__62
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_x3__83
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_x3__83_term ]
let def_int_of_4bits_out__69 n =
  (*  int_of_4bits_out__69(n)  =  (int_of_4bits_int_of_bit_out__78(n) + (2 * (int_of_4bits_int_of_bit_out__79(n) + (2 * (int_of_4bits_int_of_bit_out__80(n) + (2 * int_of_4bits_int_of_bit_out__81(n)))))))  *)
  let int_of_4bits_out__69_term = Term.make_arith Term.Plus (Term.make_app int_of_4bits_int_of_bit_out__78
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ) (Term.make_arith Term.Mult (Term.make_int (Num.Int 2)) (Term.make_arith Term.Plus (Term.make_app int_of_4bits_int_of_bit_out__79
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ) (Term.make_arith Term.Mult (Term.make_int (Num.Int 2)) (Term.make_arith Term.Plus (Term.make_app int_of_4bits_int_of_bit_out__80
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ) (Term.make_arith Term.Mult (Term.make_int (Num.Int 2)) (Term.make_app int_of_4bits_int_of_bit_out__81
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ))))))
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_out__69
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_out__69_term ]
let def_int_of_4bits_int_of_bit_x__82 n =
  (*  int_of_4bits_int_of_bit_x__82(n)  =  int_of_4bits_x3__83(n)  *)
  let int_of_4bits_int_of_bit_x__82_term = Term.make_app int_of_4bits_x3__83
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__82
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_x__82_term ]
let def_int_of_4bits_int_of_bit_out__81 n =
  (*  int_of_4bits_int_of_bit_out__81(n)  =  (if int_of_4bits_int_of_bit_x__82(n) then 1 else 0)  *)
  let int_of_4bits_int_of_bit_out__81_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__82
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ])
    (Term.make_int (Num.Int 1))
    (Term.make_int (Num.Int 0))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_out__81
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_out__81_term ]
let def_int_of_4bits_int_of_bit_x__84 n =
  (*  int_of_4bits_int_of_bit_x__84(n)  =  int_of_4bits_x2__85(n)  *)
  let int_of_4bits_int_of_bit_x__84_term = Term.make_app int_of_4bits_x2__85
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__84
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_x__84_term ]
let def_int_of_4bits_int_of_bit_out__80 n =
  (*  int_of_4bits_int_of_bit_out__80(n)  =  (if int_of_4bits_int_of_bit_x__84(n) then 1 else 0)  *)
  let int_of_4bits_int_of_bit_out__80_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__84
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ])
    (Term.make_int (Num.Int 1))
    (Term.make_int (Num.Int 0))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_out__80
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_out__80_term ]
let def_int_of_4bits_int_of_bit_x__86 n =
  (*  int_of_4bits_int_of_bit_x__86(n)  =  int_of_4bits_x1__87(n)  *)
  let int_of_4bits_int_of_bit_x__86_term = Term.make_app int_of_4bits_x1__87
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__86
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_x__86_term ]
let def_int_of_4bits_int_of_bit_out__79 n =
  (*  int_of_4bits_int_of_bit_out__79(n)  =  (if int_of_4bits_int_of_bit_x__86(n) then 1 else 0)  *)
  let int_of_4bits_int_of_bit_out__79_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__86
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ])
    (Term.make_int (Num.Int 1))
    (Term.make_int (Num.Int 0))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_out__79
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_out__79_term ]
let def_int_of_4bits_int_of_bit_x__88 n =
  (*  int_of_4bits_int_of_bit_x__88(n)  =  int_of_4bits_x0__89(n)  *)
  let int_of_4bits_int_of_bit_x__88_term = Term.make_app int_of_4bits_x0__89
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__88
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_x__88_term ]
let def_int_of_4bits_int_of_bit_out__78 n =
  (*  int_of_4bits_int_of_bit_out__78(n)  =  (if int_of_4bits_int_of_bit_x__88(n) then 1 else 0)  *)
  let int_of_4bits_int_of_bit_out__78_term = Term.make_ite
    (Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_x__88
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ])
    (Term.make_int (Num.Int 1))
    (Term.make_int (Num.Int 0))
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app int_of_4bits_int_of_bit_out__78
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; int_of_4bits_int_of_bit_out__78_term ]
let def_inc4_x0__353 n =
  (*  inc4_x0__353(n)  =  x0__59(n-1)  *)
  let inc4_x0__353_term = Term.make_app x0__59
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_x0__353
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_x0__353_term ]
let def_inc4_x1__355 n =
  (*  inc4_x1__355(n)  =  x1__60(n-1)  *)
  let inc4_x1__355_term = Term.make_app x1__60
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_x1__355
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_x1__355_term ]
let def_inc4_x2__357 n =
  (*  inc4_x2__357(n)  =  x2__61(n-1)  *)
  let inc4_x2__357_term = Term.make_app x2__61
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_x2__357
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_x2__357_term ]
let def_inc4_x3__359 n =
  (*  inc4_x3__359(n)  =  x3__62(n-1)  *)
  let inc4_x3__359_term = Term.make_app x3__62
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_x3__359
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_x3__359_term ]
let def_inc4_out3__68 n =
  (*  inc4_out3__68(n)  =  inc4_add4_out3__348(n)  *)
  let inc4_out3__68_term = Term.make_app inc4_add4_out3__348
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_out3__68
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_out3__68_term ]
let def_inc4_out2__67 n =
  (*  inc4_out2__67(n)  =  inc4_add4_out2__349(n)  *)
  let inc4_out2__67_term = Term.make_app inc4_add4_out2__349
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_out2__67
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_out2__67_term ]
let def_inc4_out1__66 n =
  (*  inc4_out1__66(n)  =  inc4_add4_out1__350(n)  *)
  let inc4_out1__66_term = Term.make_app inc4_add4_out1__350
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_out1__66
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_out1__66_term ]
let def_inc4_out0__65 n =
  (*  inc4_out0__65(n)  =  inc4_add4_out0__351(n)  *)
  let inc4_out0__65_term = Term.make_app inc4_add4_out0__351
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_out0__65
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_out0__65_term ]
let def_inc4_add4_a0__352 n =
  (*  inc4_add4_a0__352(n)  =  inc4_x0__353(n)  *)
  let inc4_add4_a0__352_term = Term.make_app inc4_x0__353
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_a0__352
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_a0__352_term ]
let def_inc4_add4_a1__354 n =
  (*  inc4_add4_a1__354(n)  =  inc4_x1__355(n)  *)
  let inc4_add4_a1__354_term = Term.make_app inc4_x1__355
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_a1__354
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_a1__354_term ]
let def_inc4_add4_a2__356 n =
  (*  inc4_add4_a2__356(n)  =  inc4_x2__357(n)  *)
  let inc4_add4_a2__356_term = Term.make_app inc4_x2__357
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_a2__356
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_a2__356_term ]
let def_inc4_add4_a3__358 n =
  (*  inc4_add4_a3__358(n)  =  inc4_x3__359(n)  *)
  let inc4_add4_a3__358_term = Term.make_app inc4_x3__359
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_a3__358
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_a3__358_term ]
let def_inc4_add4_b0__360 n =
  (*  inc4_add4_b0__360(n)  =  true  *)
  let inc4_add4_b0__360_term = Term.t_true
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_b0__360
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_b0__360_term ]
let def_inc4_add4_b1__361 n =
  (*  inc4_add4_b1__361(n)  =  false  *)
  let inc4_add4_b1__361_term = Term.t_false
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_b1__361
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_b1__361_term ]
let def_inc4_add4_b2__362 n =
  (*  inc4_add4_b2__362(n)  =  false  *)
  let inc4_add4_b2__362_term = Term.t_false
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_b2__362
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_b2__362_term ]
let def_inc4_add4_b3__363 n =
  (*  inc4_add4_b3__363(n)  =  false  *)
  let inc4_add4_b3__363_term = Term.t_false
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_b3__363
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_b3__363_term ]
let def_inc4_add4_c__364 n =
  (*  inc4_add4_c__364(n)  =  false  *)
  let inc4_add4_c__364_term = Term.t_false
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_c__364
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_c__364_term ]
let def_inc4_add4_c0__365 n =
  (*  inc4_add4_c0__365(n)  =  inc4_add4_fulladder_carry__366(n)  *)
  let inc4_add4_c0__365_term = Term.make_app inc4_add4_fulladder_carry__366
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_c0__365
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_c0__365_term ]
let def_inc4_add4_out0__351 n =
  (*  inc4_add4_out0__351(n)  =  inc4_add4_fulladder_sum__367(n)  *)
  let inc4_add4_out0__351_term = Term.make_app inc4_add4_fulladder_sum__367
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_out0__351
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_out0__351_term ]
let def_inc4_add4_c1__368 n =
  (*  inc4_add4_c1__368(n)  =  inc4_add4_fulladder_carry__369(n)  *)
  let inc4_add4_c1__368_term = Term.make_app inc4_add4_fulladder_carry__369
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_c1__368
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_c1__368_term ]
let def_inc4_add4_out1__350 n =
  (*  inc4_add4_out1__350(n)  =  inc4_add4_fulladder_sum__370(n)  *)
  let inc4_add4_out1__350_term = Term.make_app inc4_add4_fulladder_sum__370
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_out1__350
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_out1__350_term ]
let def_inc4_add4_c2__371 n =
  (*  inc4_add4_c2__371(n)  =  inc4_add4_fulladder_carry__372(n)  *)
  let inc4_add4_c2__371_term = Term.make_app inc4_add4_fulladder_carry__372
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_c2__371
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_c2__371_term ]
let def_inc4_add4_out2__349 n =
  (*  inc4_add4_out2__349(n)  =  inc4_add4_fulladder_sum__373(n)  *)
  let inc4_add4_out2__349_term = Term.make_app inc4_add4_fulladder_sum__373
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_out2__349
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_out2__349_term ]
let def_inc4_add4_c3__374 n =
  (*  inc4_add4_c3__374(n)  =  inc4_add4_fulladder_carry__375(n)  *)
  let inc4_add4_c3__374_term = Term.make_app inc4_add4_fulladder_carry__375
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_c3__374
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_c3__374_term ]
let def_inc4_add4_out3__348 n =
  (*  inc4_add4_out3__348(n)  =  inc4_add4_fulladder_sum__376(n)  *)
  let inc4_add4_out3__348_term = Term.make_app inc4_add4_fulladder_sum__376
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_out3__348
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_out3__348_term ]
let def_inc4_add4_fulladder_a__377 n =
  (*  inc4_add4_fulladder_a__377(n)  =  inc4_add4_a3__358(n)  *)
  let inc4_add4_fulladder_a__377_term = Term.make_app inc4_add4_a3__358
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_a__377
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_a__377_term ]
let def_inc4_add4_fulladder_b__378 n =
  (*  inc4_add4_fulladder_b__378(n)  =  inc4_add4_b3__363(n)  *)
  let inc4_add4_fulladder_b__378_term = Term.make_app inc4_add4_b3__363
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_b__378
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_b__378_term ]
let def_inc4_add4_fulladder_c__379 n =
  (*  inc4_add4_fulladder_c__379(n)  =  inc4_add4_c2__371(n)  *)
  let inc4_add4_fulladder_c__379_term = Term.make_app inc4_add4_c2__371
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c__379
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c__379_term ]
let def_inc4_add4_fulladder_c1__380 n =
  (*  inc4_add4_fulladder_c1__380(n)  =  inc4_add4_fulladder_halfadder_carry__381(n)  *)
  let inc4_add4_fulladder_c1__380_term = Term.make_app inc4_add4_fulladder_halfadder_carry__381
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__380
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c1__380_term ]
let def_inc4_add4_fulladder_s1__382 n =
  (*  inc4_add4_fulladder_s1__382(n)  =  inc4_add4_fulladder_halfadder_sum__383(n)  *)
  let inc4_add4_fulladder_s1__382_term = Term.make_app inc4_add4_fulladder_halfadder_sum__383
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_s1__382
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_s1__382_term ]
let def_inc4_add4_fulladder_c2__384 n =
  (*  inc4_add4_fulladder_c2__384(n)  =  inc4_add4_fulladder_halfadder_carry__385(n)  *)
  let inc4_add4_fulladder_c2__384_term = Term.make_app inc4_add4_fulladder_halfadder_carry__385
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__384
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c2__384_term ]
let def_inc4_add4_fulladder_sum__376 n =
  (*  inc4_add4_fulladder_sum__376(n)  =  inc4_add4_fulladder_halfadder_sum__386(n)  *)
  let inc4_add4_fulladder_sum__376_term = Term.make_app inc4_add4_fulladder_halfadder_sum__386
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_sum__376
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_sum__376_term ]
let def_inc4_add4_fulladder_carry__375 n =
  (*  inc4_add4_fulladder_carry__375(n)  =  inc4_add4_fulladder_aux__387(n)  *)
  let inc4_add4_fulladder_carry__375_term = Term.make_app inc4_add4_fulladder_aux__387
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_carry__375
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_carry__375_term ]
let def_inc4_add4_fulladder_aux__387 n =
  (*  (inc4_add4_fulladder_aux__387(n)  ==>  (inc4_add4_fulladder_c1__380(n) || inc4_add4_fulladder_c2__384(n)))  &&  ((inc4_add4_fulladder_c1__380(n) || inc4_add4_fulladder_c2__384(n))  ==>  inc4_add4_fulladder_aux__387(n))  *)
  let inc4_add4_fulladder_aux__387_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_aux__387
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_aux__387_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__380
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__384
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__387_n; inc4_add4_fulladder_aux__387_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__387_formula; inc4_add4_fulladder_aux__387_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__388 n =
  (*  inc4_add4_fulladder_halfadder_a__388(n)  =  inc4_add4_fulladder_c__379(n)  *)
  let inc4_add4_fulladder_halfadder_a__388_term = Term.make_app inc4_add4_fulladder_c__379
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__388
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__388_term ]
let def_inc4_add4_fulladder_halfadder_b__389 n =
  (*  inc4_add4_fulladder_halfadder_b__389(n)  =  inc4_add4_fulladder_s1__382(n)  *)
  let inc4_add4_fulladder_halfadder_b__389_term = Term.make_app inc4_add4_fulladder_s1__382
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__389
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__389_term ]
let def_inc4_add4_fulladder_halfadder_sum__386 n =
  (*  inc4_add4_fulladder_halfadder_sum__386(n)  =  inc4_add4_fulladder_halfadder_xor_out__390(n)  *)
  let inc4_add4_fulladder_halfadder_sum__386_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__390
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__386
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__386_term ]
let def_inc4_add4_fulladder_halfadder_carry__385 n =
  (*  inc4_add4_fulladder_halfadder_carry__385(n)  =  inc4_add4_fulladder_halfadder_aux__391(n)  *)
  let inc4_add4_fulladder_halfadder_carry__385_term = Term.make_app inc4_add4_fulladder_halfadder_aux__391
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__385
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__385_term ]
let def_inc4_add4_fulladder_halfadder_aux__391 n =
  (*  (inc4_add4_fulladder_halfadder_aux__391(n)  ==>  (inc4_add4_fulladder_halfadder_a__388(n) && inc4_add4_fulladder_halfadder_b__389(n)))  &&  ((inc4_add4_fulladder_halfadder_a__388(n) && inc4_add4_fulladder_halfadder_b__389(n))  ==>  inc4_add4_fulladder_halfadder_aux__391(n))  *)
  let inc4_add4_fulladder_halfadder_aux__391_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__391
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__391_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__388
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__389
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__391_n; inc4_add4_fulladder_halfadder_aux__391_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__391_formula; inc4_add4_fulladder_halfadder_aux__391_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__392 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__392(n)  =  inc4_add4_fulladder_halfadder_a__388(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__392_term = Term.make_app inc4_add4_fulladder_halfadder_a__388
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__392
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__392_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__393 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__393(n)  =  inc4_add4_fulladder_halfadder_b__389(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__393_term = Term.make_app inc4_add4_fulladder_halfadder_b__389
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__393
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__393_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__390 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__390(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__392(n) && inc4_add4_fulladder_halfadder_xor_b__393(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__394(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__390_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__392
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__393
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__394
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__390
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__390_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__394 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__394(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__392(n) || inc4_add4_fulladder_halfadder_xor_b__393(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__392(n) || inc4_add4_fulladder_halfadder_xor_b__393(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__394(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__394_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__394
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__394_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__392
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__393
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__394_n; inc4_add4_fulladder_halfadder_xor_aux__394_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__394_formula; inc4_add4_fulladder_halfadder_xor_aux__394_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__395 n =
  (*  inc4_add4_fulladder_halfadder_a__395(n)  =  inc4_add4_fulladder_a__377(n)  *)
  let inc4_add4_fulladder_halfadder_a__395_term = Term.make_app inc4_add4_fulladder_a__377
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__395
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__395_term ]
let def_inc4_add4_fulladder_halfadder_b__396 n =
  (*  inc4_add4_fulladder_halfadder_b__396(n)  =  inc4_add4_fulladder_b__378(n)  *)
  let inc4_add4_fulladder_halfadder_b__396_term = Term.make_app inc4_add4_fulladder_b__378
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__396
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__396_term ]
let def_inc4_add4_fulladder_halfadder_sum__383 n =
  (*  inc4_add4_fulladder_halfadder_sum__383(n)  =  inc4_add4_fulladder_halfadder_xor_out__397(n)  *)
  let inc4_add4_fulladder_halfadder_sum__383_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__397
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__383
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__383_term ]
let def_inc4_add4_fulladder_halfadder_carry__381 n =
  (*  inc4_add4_fulladder_halfadder_carry__381(n)  =  inc4_add4_fulladder_halfadder_aux__398(n)  *)
  let inc4_add4_fulladder_halfadder_carry__381_term = Term.make_app inc4_add4_fulladder_halfadder_aux__398
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__381
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__381_term ]
let def_inc4_add4_fulladder_halfadder_aux__398 n =
  (*  (inc4_add4_fulladder_halfadder_aux__398(n)  ==>  (inc4_add4_fulladder_halfadder_a__395(n) && inc4_add4_fulladder_halfadder_b__396(n)))  &&  ((inc4_add4_fulladder_halfadder_a__395(n) && inc4_add4_fulladder_halfadder_b__396(n))  ==>  inc4_add4_fulladder_halfadder_aux__398(n))  *)
  let inc4_add4_fulladder_halfadder_aux__398_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__398
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__398_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__395
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__396
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__398_n; inc4_add4_fulladder_halfadder_aux__398_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__398_formula; inc4_add4_fulladder_halfadder_aux__398_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__399 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__399(n)  =  inc4_add4_fulladder_halfadder_a__395(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__399_term = Term.make_app inc4_add4_fulladder_halfadder_a__395
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__399
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__399_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__400 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__400(n)  =  inc4_add4_fulladder_halfadder_b__396(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__400_term = Term.make_app inc4_add4_fulladder_halfadder_b__396
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__400
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__400_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__397 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__397(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__399(n) && inc4_add4_fulladder_halfadder_xor_b__400(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__401(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__397_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__399
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__400
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__401
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__397
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__397_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__401 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__401(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__399(n) || inc4_add4_fulladder_halfadder_xor_b__400(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__399(n) || inc4_add4_fulladder_halfadder_xor_b__400(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__401(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__401_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__401
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__401_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__399
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__400
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__401_n; inc4_add4_fulladder_halfadder_xor_aux__401_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__401_formula; inc4_add4_fulladder_halfadder_xor_aux__401_n ]
   ]


let def_inc4_add4_fulladder_a__402 n =
  (*  inc4_add4_fulladder_a__402(n)  =  inc4_add4_a2__356(n)  *)
  let inc4_add4_fulladder_a__402_term = Term.make_app inc4_add4_a2__356
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_a__402
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_a__402_term ]
let def_inc4_add4_fulladder_b__403 n =
  (*  inc4_add4_fulladder_b__403(n)  =  inc4_add4_b2__362(n)  *)
  let inc4_add4_fulladder_b__403_term = Term.make_app inc4_add4_b2__362
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_b__403
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_b__403_term ]
let def_inc4_add4_fulladder_c__404 n =
  (*  inc4_add4_fulladder_c__404(n)  =  inc4_add4_c1__368(n)  *)
  let inc4_add4_fulladder_c__404_term = Term.make_app inc4_add4_c1__368
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c__404
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c__404_term ]
let def_inc4_add4_fulladder_c1__405 n =
  (*  inc4_add4_fulladder_c1__405(n)  =  inc4_add4_fulladder_halfadder_carry__406(n)  *)
  let inc4_add4_fulladder_c1__405_term = Term.make_app inc4_add4_fulladder_halfadder_carry__406
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__405
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c1__405_term ]
let def_inc4_add4_fulladder_s1__407 n =
  (*  inc4_add4_fulladder_s1__407(n)  =  inc4_add4_fulladder_halfadder_sum__408(n)  *)
  let inc4_add4_fulladder_s1__407_term = Term.make_app inc4_add4_fulladder_halfadder_sum__408
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_s1__407
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_s1__407_term ]
let def_inc4_add4_fulladder_c2__409 n =
  (*  inc4_add4_fulladder_c2__409(n)  =  inc4_add4_fulladder_halfadder_carry__410(n)  *)
  let inc4_add4_fulladder_c2__409_term = Term.make_app inc4_add4_fulladder_halfadder_carry__410
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__409
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c2__409_term ]
let def_inc4_add4_fulladder_sum__373 n =
  (*  inc4_add4_fulladder_sum__373(n)  =  inc4_add4_fulladder_halfadder_sum__411(n)  *)
  let inc4_add4_fulladder_sum__373_term = Term.make_app inc4_add4_fulladder_halfadder_sum__411
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_sum__373
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_sum__373_term ]
let def_inc4_add4_fulladder_carry__372 n =
  (*  inc4_add4_fulladder_carry__372(n)  =  inc4_add4_fulladder_aux__412(n)  *)
  let inc4_add4_fulladder_carry__372_term = Term.make_app inc4_add4_fulladder_aux__412
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_carry__372
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_carry__372_term ]
let def_inc4_add4_fulladder_aux__412 n =
  (*  (inc4_add4_fulladder_aux__412(n)  ==>  (inc4_add4_fulladder_c1__405(n) || inc4_add4_fulladder_c2__409(n)))  &&  ((inc4_add4_fulladder_c1__405(n) || inc4_add4_fulladder_c2__409(n))  ==>  inc4_add4_fulladder_aux__412(n))  *)
  let inc4_add4_fulladder_aux__412_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_aux__412
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_aux__412_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__405
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__409
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__412_n; inc4_add4_fulladder_aux__412_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__412_formula; inc4_add4_fulladder_aux__412_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__413 n =
  (*  inc4_add4_fulladder_halfadder_a__413(n)  =  inc4_add4_fulladder_c__404(n)  *)
  let inc4_add4_fulladder_halfadder_a__413_term = Term.make_app inc4_add4_fulladder_c__404
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__413
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__413_term ]
let def_inc4_add4_fulladder_halfadder_b__414 n =
  (*  inc4_add4_fulladder_halfadder_b__414(n)  =  inc4_add4_fulladder_s1__407(n)  *)
  let inc4_add4_fulladder_halfadder_b__414_term = Term.make_app inc4_add4_fulladder_s1__407
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__414
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__414_term ]
let def_inc4_add4_fulladder_halfadder_sum__411 n =
  (*  inc4_add4_fulladder_halfadder_sum__411(n)  =  inc4_add4_fulladder_halfadder_xor_out__415(n)  *)
  let inc4_add4_fulladder_halfadder_sum__411_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__415
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__411
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__411_term ]
let def_inc4_add4_fulladder_halfadder_carry__410 n =
  (*  inc4_add4_fulladder_halfadder_carry__410(n)  =  inc4_add4_fulladder_halfadder_aux__416(n)  *)
  let inc4_add4_fulladder_halfadder_carry__410_term = Term.make_app inc4_add4_fulladder_halfadder_aux__416
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__410
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__410_term ]
let def_inc4_add4_fulladder_halfadder_aux__416 n =
  (*  (inc4_add4_fulladder_halfadder_aux__416(n)  ==>  (inc4_add4_fulladder_halfadder_a__413(n) && inc4_add4_fulladder_halfadder_b__414(n)))  &&  ((inc4_add4_fulladder_halfadder_a__413(n) && inc4_add4_fulladder_halfadder_b__414(n))  ==>  inc4_add4_fulladder_halfadder_aux__416(n))  *)
  let inc4_add4_fulladder_halfadder_aux__416_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__416
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__416_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__413
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__414
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__416_n; inc4_add4_fulladder_halfadder_aux__416_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__416_formula; inc4_add4_fulladder_halfadder_aux__416_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__417 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__417(n)  =  inc4_add4_fulladder_halfadder_a__413(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__417_term = Term.make_app inc4_add4_fulladder_halfadder_a__413
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__417
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__417_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__418 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__418(n)  =  inc4_add4_fulladder_halfadder_b__414(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__418_term = Term.make_app inc4_add4_fulladder_halfadder_b__414
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__418
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__418_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__415 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__415(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__417(n) && inc4_add4_fulladder_halfadder_xor_b__418(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__419(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__415_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__417
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__418
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__419
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__415
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__415_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__419 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__419(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__417(n) || inc4_add4_fulladder_halfadder_xor_b__418(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__417(n) || inc4_add4_fulladder_halfadder_xor_b__418(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__419(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__419_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__419
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__419_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__417
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__418
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__419_n; inc4_add4_fulladder_halfadder_xor_aux__419_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__419_formula; inc4_add4_fulladder_halfadder_xor_aux__419_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__420 n =
  (*  inc4_add4_fulladder_halfadder_a__420(n)  =  inc4_add4_fulladder_a__402(n)  *)
  let inc4_add4_fulladder_halfadder_a__420_term = Term.make_app inc4_add4_fulladder_a__402
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__420
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__420_term ]
let def_inc4_add4_fulladder_halfadder_b__421 n =
  (*  inc4_add4_fulladder_halfadder_b__421(n)  =  inc4_add4_fulladder_b__403(n)  *)
  let inc4_add4_fulladder_halfadder_b__421_term = Term.make_app inc4_add4_fulladder_b__403
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__421
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__421_term ]
let def_inc4_add4_fulladder_halfadder_sum__408 n =
  (*  inc4_add4_fulladder_halfadder_sum__408(n)  =  inc4_add4_fulladder_halfadder_xor_out__422(n)  *)
  let inc4_add4_fulladder_halfadder_sum__408_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__422
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__408
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__408_term ]
let def_inc4_add4_fulladder_halfadder_carry__406 n =
  (*  inc4_add4_fulladder_halfadder_carry__406(n)  =  inc4_add4_fulladder_halfadder_aux__423(n)  *)
  let inc4_add4_fulladder_halfadder_carry__406_term = Term.make_app inc4_add4_fulladder_halfadder_aux__423
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__406
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__406_term ]
let def_inc4_add4_fulladder_halfadder_aux__423 n =
  (*  (inc4_add4_fulladder_halfadder_aux__423(n)  ==>  (inc4_add4_fulladder_halfadder_a__420(n) && inc4_add4_fulladder_halfadder_b__421(n)))  &&  ((inc4_add4_fulladder_halfadder_a__420(n) && inc4_add4_fulladder_halfadder_b__421(n))  ==>  inc4_add4_fulladder_halfadder_aux__423(n))  *)
  let inc4_add4_fulladder_halfadder_aux__423_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__423
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__423_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__420
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__421
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__423_n; inc4_add4_fulladder_halfadder_aux__423_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__423_formula; inc4_add4_fulladder_halfadder_aux__423_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__424 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__424(n)  =  inc4_add4_fulladder_halfadder_a__420(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__424_term = Term.make_app inc4_add4_fulladder_halfadder_a__420
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__424
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__424_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__425 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__425(n)  =  inc4_add4_fulladder_halfadder_b__421(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__425_term = Term.make_app inc4_add4_fulladder_halfadder_b__421
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__425
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__425_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__422 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__422(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__424(n) && inc4_add4_fulladder_halfadder_xor_b__425(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__426(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__422_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__424
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__425
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__426
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__422
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__422_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__426 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__426(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__424(n) || inc4_add4_fulladder_halfadder_xor_b__425(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__424(n) || inc4_add4_fulladder_halfadder_xor_b__425(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__426(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__426_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__426
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__426_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__424
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__425
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__426_n; inc4_add4_fulladder_halfadder_xor_aux__426_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__426_formula; inc4_add4_fulladder_halfadder_xor_aux__426_n ]
   ]


let def_inc4_add4_fulladder_a__427 n =
  (*  inc4_add4_fulladder_a__427(n)  =  inc4_add4_a1__354(n)  *)
  let inc4_add4_fulladder_a__427_term = Term.make_app inc4_add4_a1__354
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_a__427
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_a__427_term ]
let def_inc4_add4_fulladder_b__428 n =
  (*  inc4_add4_fulladder_b__428(n)  =  inc4_add4_b1__361(n)  *)
  let inc4_add4_fulladder_b__428_term = Term.make_app inc4_add4_b1__361
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_b__428
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_b__428_term ]
let def_inc4_add4_fulladder_c__429 n =
  (*  inc4_add4_fulladder_c__429(n)  =  inc4_add4_c0__365(n)  *)
  let inc4_add4_fulladder_c__429_term = Term.make_app inc4_add4_c0__365
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c__429
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c__429_term ]
let def_inc4_add4_fulladder_c1__430 n =
  (*  inc4_add4_fulladder_c1__430(n)  =  inc4_add4_fulladder_halfadder_carry__431(n)  *)
  let inc4_add4_fulladder_c1__430_term = Term.make_app inc4_add4_fulladder_halfadder_carry__431
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__430
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c1__430_term ]
let def_inc4_add4_fulladder_s1__432 n =
  (*  inc4_add4_fulladder_s1__432(n)  =  inc4_add4_fulladder_halfadder_sum__433(n)  *)
  let inc4_add4_fulladder_s1__432_term = Term.make_app inc4_add4_fulladder_halfadder_sum__433
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_s1__432
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_s1__432_term ]
let def_inc4_add4_fulladder_c2__434 n =
  (*  inc4_add4_fulladder_c2__434(n)  =  inc4_add4_fulladder_halfadder_carry__435(n)  *)
  let inc4_add4_fulladder_c2__434_term = Term.make_app inc4_add4_fulladder_halfadder_carry__435
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__434
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c2__434_term ]
let def_inc4_add4_fulladder_sum__370 n =
  (*  inc4_add4_fulladder_sum__370(n)  =  inc4_add4_fulladder_halfadder_sum__436(n)  *)
  let inc4_add4_fulladder_sum__370_term = Term.make_app inc4_add4_fulladder_halfadder_sum__436
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_sum__370
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_sum__370_term ]
let def_inc4_add4_fulladder_carry__369 n =
  (*  inc4_add4_fulladder_carry__369(n)  =  inc4_add4_fulladder_aux__437(n)  *)
  let inc4_add4_fulladder_carry__369_term = Term.make_app inc4_add4_fulladder_aux__437
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_carry__369
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_carry__369_term ]
let def_inc4_add4_fulladder_aux__437 n =
  (*  (inc4_add4_fulladder_aux__437(n)  ==>  (inc4_add4_fulladder_c1__430(n) || inc4_add4_fulladder_c2__434(n)))  &&  ((inc4_add4_fulladder_c1__430(n) || inc4_add4_fulladder_c2__434(n))  ==>  inc4_add4_fulladder_aux__437(n))  *)
  let inc4_add4_fulladder_aux__437_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_aux__437
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_aux__437_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__430
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__434
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__437_n; inc4_add4_fulladder_aux__437_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__437_formula; inc4_add4_fulladder_aux__437_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__438 n =
  (*  inc4_add4_fulladder_halfadder_a__438(n)  =  inc4_add4_fulladder_c__429(n)  *)
  let inc4_add4_fulladder_halfadder_a__438_term = Term.make_app inc4_add4_fulladder_c__429
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__438
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__438_term ]
let def_inc4_add4_fulladder_halfadder_b__439 n =
  (*  inc4_add4_fulladder_halfadder_b__439(n)  =  inc4_add4_fulladder_s1__432(n)  *)
  let inc4_add4_fulladder_halfadder_b__439_term = Term.make_app inc4_add4_fulladder_s1__432
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__439
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__439_term ]
let def_inc4_add4_fulladder_halfadder_sum__436 n =
  (*  inc4_add4_fulladder_halfadder_sum__436(n)  =  inc4_add4_fulladder_halfadder_xor_out__440(n)  *)
  let inc4_add4_fulladder_halfadder_sum__436_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__440
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__436
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__436_term ]
let def_inc4_add4_fulladder_halfadder_carry__435 n =
  (*  inc4_add4_fulladder_halfadder_carry__435(n)  =  inc4_add4_fulladder_halfadder_aux__441(n)  *)
  let inc4_add4_fulladder_halfadder_carry__435_term = Term.make_app inc4_add4_fulladder_halfadder_aux__441
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__435
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__435_term ]
let def_inc4_add4_fulladder_halfadder_aux__441 n =
  (*  (inc4_add4_fulladder_halfadder_aux__441(n)  ==>  (inc4_add4_fulladder_halfadder_a__438(n) && inc4_add4_fulladder_halfadder_b__439(n)))  &&  ((inc4_add4_fulladder_halfadder_a__438(n) && inc4_add4_fulladder_halfadder_b__439(n))  ==>  inc4_add4_fulladder_halfadder_aux__441(n))  *)
  let inc4_add4_fulladder_halfadder_aux__441_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__441
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__441_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__438
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__439
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__441_n; inc4_add4_fulladder_halfadder_aux__441_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__441_formula; inc4_add4_fulladder_halfadder_aux__441_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__442 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__442(n)  =  inc4_add4_fulladder_halfadder_a__438(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__442_term = Term.make_app inc4_add4_fulladder_halfadder_a__438
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__442
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__442_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__443 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__443(n)  =  inc4_add4_fulladder_halfadder_b__439(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__443_term = Term.make_app inc4_add4_fulladder_halfadder_b__439
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__443
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__443_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__440 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__440(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__442(n) && inc4_add4_fulladder_halfadder_xor_b__443(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__444(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__440_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__442
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__443
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__444
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__440
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__440_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__444 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__444(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__442(n) || inc4_add4_fulladder_halfadder_xor_b__443(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__442(n) || inc4_add4_fulladder_halfadder_xor_b__443(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__444(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__444_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__444
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__444_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__442
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__443
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__444_n; inc4_add4_fulladder_halfadder_xor_aux__444_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__444_formula; inc4_add4_fulladder_halfadder_xor_aux__444_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__445 n =
  (*  inc4_add4_fulladder_halfadder_a__445(n)  =  inc4_add4_fulladder_a__427(n)  *)
  let inc4_add4_fulladder_halfadder_a__445_term = Term.make_app inc4_add4_fulladder_a__427
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__445
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__445_term ]
let def_inc4_add4_fulladder_halfadder_b__446 n =
  (*  inc4_add4_fulladder_halfadder_b__446(n)  =  inc4_add4_fulladder_b__428(n)  *)
  let inc4_add4_fulladder_halfadder_b__446_term = Term.make_app inc4_add4_fulladder_b__428
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__446
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__446_term ]
let def_inc4_add4_fulladder_halfadder_sum__433 n =
  (*  inc4_add4_fulladder_halfadder_sum__433(n)  =  inc4_add4_fulladder_halfadder_xor_out__447(n)  *)
  let inc4_add4_fulladder_halfadder_sum__433_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__447
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__433
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__433_term ]
let def_inc4_add4_fulladder_halfadder_carry__431 n =
  (*  inc4_add4_fulladder_halfadder_carry__431(n)  =  inc4_add4_fulladder_halfadder_aux__448(n)  *)
  let inc4_add4_fulladder_halfadder_carry__431_term = Term.make_app inc4_add4_fulladder_halfadder_aux__448
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__431
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__431_term ]
let def_inc4_add4_fulladder_halfadder_aux__448 n =
  (*  (inc4_add4_fulladder_halfadder_aux__448(n)  ==>  (inc4_add4_fulladder_halfadder_a__445(n) && inc4_add4_fulladder_halfadder_b__446(n)))  &&  ((inc4_add4_fulladder_halfadder_a__445(n) && inc4_add4_fulladder_halfadder_b__446(n))  ==>  inc4_add4_fulladder_halfadder_aux__448(n))  *)
  let inc4_add4_fulladder_halfadder_aux__448_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__448
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__448_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__445
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__446
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__448_n; inc4_add4_fulladder_halfadder_aux__448_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__448_formula; inc4_add4_fulladder_halfadder_aux__448_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__449 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__449(n)  =  inc4_add4_fulladder_halfadder_a__445(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__449_term = Term.make_app inc4_add4_fulladder_halfadder_a__445
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__449
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__449_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__450 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__450(n)  =  inc4_add4_fulladder_halfadder_b__446(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__450_term = Term.make_app inc4_add4_fulladder_halfadder_b__446
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__450
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__450_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__447 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__447(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__449(n) && inc4_add4_fulladder_halfadder_xor_b__450(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__451(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__447_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__449
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__450
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__451
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__447
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__447_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__451 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__451(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__449(n) || inc4_add4_fulladder_halfadder_xor_b__450(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__449(n) || inc4_add4_fulladder_halfadder_xor_b__450(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__451(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__451_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__451
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__451_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__449
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__450
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__451_n; inc4_add4_fulladder_halfadder_xor_aux__451_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__451_formula; inc4_add4_fulladder_halfadder_xor_aux__451_n ]
   ]


let def_inc4_add4_fulladder_a__452 n =
  (*  inc4_add4_fulladder_a__452(n)  =  inc4_add4_a0__352(n)  *)
  let inc4_add4_fulladder_a__452_term = Term.make_app inc4_add4_a0__352
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_a__452
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_a__452_term ]
let def_inc4_add4_fulladder_b__453 n =
  (*  inc4_add4_fulladder_b__453(n)  =  inc4_add4_b0__360(n)  *)
  let inc4_add4_fulladder_b__453_term = Term.make_app inc4_add4_b0__360
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_b__453
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_b__453_term ]
let def_inc4_add4_fulladder_c__454 n =
  (*  inc4_add4_fulladder_c__454(n)  =  inc4_add4_c__364(n)  *)
  let inc4_add4_fulladder_c__454_term = Term.make_app inc4_add4_c__364
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c__454
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c__454_term ]
let def_inc4_add4_fulladder_c1__455 n =
  (*  inc4_add4_fulladder_c1__455(n)  =  inc4_add4_fulladder_halfadder_carry__456(n)  *)
  let inc4_add4_fulladder_c1__455_term = Term.make_app inc4_add4_fulladder_halfadder_carry__456
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__455
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c1__455_term ]
let def_inc4_add4_fulladder_s1__457 n =
  (*  inc4_add4_fulladder_s1__457(n)  =  inc4_add4_fulladder_halfadder_sum__458(n)  *)
  let inc4_add4_fulladder_s1__457_term = Term.make_app inc4_add4_fulladder_halfadder_sum__458
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_s1__457
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_s1__457_term ]
let def_inc4_add4_fulladder_c2__459 n =
  (*  inc4_add4_fulladder_c2__459(n)  =  inc4_add4_fulladder_halfadder_carry__460(n)  *)
  let inc4_add4_fulladder_c2__459_term = Term.make_app inc4_add4_fulladder_halfadder_carry__460
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__459
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_c2__459_term ]
let def_inc4_add4_fulladder_sum__367 n =
  (*  inc4_add4_fulladder_sum__367(n)  =  inc4_add4_fulladder_halfadder_sum__461(n)  *)
  let inc4_add4_fulladder_sum__367_term = Term.make_app inc4_add4_fulladder_halfadder_sum__461
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_sum__367
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_sum__367_term ]
let def_inc4_add4_fulladder_carry__366 n =
  (*  inc4_add4_fulladder_carry__366(n)  =  inc4_add4_fulladder_aux__462(n)  *)
  let inc4_add4_fulladder_carry__366_term = Term.make_app inc4_add4_fulladder_aux__462
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_carry__366
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_carry__366_term ]
let def_inc4_add4_fulladder_aux__462 n =
  (*  (inc4_add4_fulladder_aux__462(n)  ==>  (inc4_add4_fulladder_c1__455(n) || inc4_add4_fulladder_c2__459(n)))  &&  ((inc4_add4_fulladder_c1__455(n) || inc4_add4_fulladder_c2__459(n))  ==>  inc4_add4_fulladder_aux__462(n))  *)
  let inc4_add4_fulladder_aux__462_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_aux__462
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_aux__462_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c1__455
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_c2__459
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__462_n; inc4_add4_fulladder_aux__462_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_aux__462_formula; inc4_add4_fulladder_aux__462_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__463 n =
  (*  inc4_add4_fulladder_halfadder_a__463(n)  =  inc4_add4_fulladder_c__454(n)  *)
  let inc4_add4_fulladder_halfadder_a__463_term = Term.make_app inc4_add4_fulladder_c__454
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__463
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__463_term ]
let def_inc4_add4_fulladder_halfadder_b__464 n =
  (*  inc4_add4_fulladder_halfadder_b__464(n)  =  inc4_add4_fulladder_s1__457(n)  *)
  let inc4_add4_fulladder_halfadder_b__464_term = Term.make_app inc4_add4_fulladder_s1__457
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__464
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__464_term ]
let def_inc4_add4_fulladder_halfadder_sum__461 n =
  (*  inc4_add4_fulladder_halfadder_sum__461(n)  =  inc4_add4_fulladder_halfadder_xor_out__465(n)  *)
  let inc4_add4_fulladder_halfadder_sum__461_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__465
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__461
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__461_term ]
let def_inc4_add4_fulladder_halfadder_carry__460 n =
  (*  inc4_add4_fulladder_halfadder_carry__460(n)  =  inc4_add4_fulladder_halfadder_aux__466(n)  *)
  let inc4_add4_fulladder_halfadder_carry__460_term = Term.make_app inc4_add4_fulladder_halfadder_aux__466
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__460
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__460_term ]
let def_inc4_add4_fulladder_halfadder_aux__466 n =
  (*  (inc4_add4_fulladder_halfadder_aux__466(n)  ==>  (inc4_add4_fulladder_halfadder_a__463(n) && inc4_add4_fulladder_halfadder_b__464(n)))  &&  ((inc4_add4_fulladder_halfadder_a__463(n) && inc4_add4_fulladder_halfadder_b__464(n))  ==>  inc4_add4_fulladder_halfadder_aux__466(n))  *)
  let inc4_add4_fulladder_halfadder_aux__466_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__466
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__466_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__463
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__464
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__466_n; inc4_add4_fulladder_halfadder_aux__466_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__466_formula; inc4_add4_fulladder_halfadder_aux__466_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__467 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__467(n)  =  inc4_add4_fulladder_halfadder_a__463(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__467_term = Term.make_app inc4_add4_fulladder_halfadder_a__463
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__467
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__467_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__468 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__468(n)  =  inc4_add4_fulladder_halfadder_b__464(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__468_term = Term.make_app inc4_add4_fulladder_halfadder_b__464
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__468
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__468_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__465 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__465(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__467(n) && inc4_add4_fulladder_halfadder_xor_b__468(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__469(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__465_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__467
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__468
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__469
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__465
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__465_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__469 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__469(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__467(n) || inc4_add4_fulladder_halfadder_xor_b__468(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__467(n) || inc4_add4_fulladder_halfadder_xor_b__468(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__469(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__469_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__469
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__469_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__467
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__468
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__469_n; inc4_add4_fulladder_halfadder_xor_aux__469_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__469_formula; inc4_add4_fulladder_halfadder_xor_aux__469_n ]
   ]


let def_inc4_add4_fulladder_halfadder_a__470 n =
  (*  inc4_add4_fulladder_halfadder_a__470(n)  =  inc4_add4_fulladder_a__452(n)  *)
  let inc4_add4_fulladder_halfadder_a__470_term = Term.make_app inc4_add4_fulladder_a__452
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__470
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_a__470_term ]
let def_inc4_add4_fulladder_halfadder_b__471 n =
  (*  inc4_add4_fulladder_halfadder_b__471(n)  =  inc4_add4_fulladder_b__453(n)  *)
  let inc4_add4_fulladder_halfadder_b__471_term = Term.make_app inc4_add4_fulladder_b__453
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__471
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_b__471_term ]
let def_inc4_add4_fulladder_halfadder_sum__458 n =
  (*  inc4_add4_fulladder_halfadder_sum__458(n)  =  inc4_add4_fulladder_halfadder_xor_out__472(n)  *)
  let inc4_add4_fulladder_halfadder_sum__458_term = Term.make_app inc4_add4_fulladder_halfadder_xor_out__472
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_sum__458
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_sum__458_term ]
let def_inc4_add4_fulladder_halfadder_carry__456 n =
  (*  inc4_add4_fulladder_halfadder_carry__456(n)  =  inc4_add4_fulladder_halfadder_aux__473(n)  *)
  let inc4_add4_fulladder_halfadder_carry__456_term = Term.make_app inc4_add4_fulladder_halfadder_aux__473
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_carry__456
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_carry__456_term ]
let def_inc4_add4_fulladder_halfadder_aux__473 n =
  (*  (inc4_add4_fulladder_halfadder_aux__473(n)  ==>  (inc4_add4_fulladder_halfadder_a__470(n) && inc4_add4_fulladder_halfadder_b__471(n)))  &&  ((inc4_add4_fulladder_halfadder_a__470(n) && inc4_add4_fulladder_halfadder_b__471(n))  ==>  inc4_add4_fulladder_halfadder_aux__473(n))  *)
  let inc4_add4_fulladder_halfadder_aux__473_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_aux__473
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_aux__473_formula = Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_a__470
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_b__471
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__473_n; inc4_add4_fulladder_halfadder_aux__473_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_aux__473_formula; inc4_add4_fulladder_halfadder_aux__473_n ]
   ]


let def_inc4_add4_fulladder_halfadder_xor_a__474 n =
  (*  inc4_add4_fulladder_halfadder_xor_a__474(n)  =  inc4_add4_fulladder_halfadder_a__470(n)  *)
  let inc4_add4_fulladder_halfadder_xor_a__474_term = Term.make_app inc4_add4_fulladder_halfadder_a__470
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__474
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_a__474_term ]
let def_inc4_add4_fulladder_halfadder_xor_b__475 n =
  (*  inc4_add4_fulladder_halfadder_xor_b__475(n)  =  inc4_add4_fulladder_halfadder_b__471(n)  *)
  let inc4_add4_fulladder_halfadder_xor_b__475_term = Term.make_app inc4_add4_fulladder_halfadder_b__471
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__475
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_b__475_term ]
let def_inc4_add4_fulladder_halfadder_xor_out__472 n =
  (*  inc4_add4_fulladder_halfadder_xor_out__472(n)  =  (if (inc4_add4_fulladder_halfadder_xor_a__474(n) && inc4_add4_fulladder_halfadder_xor_b__475(n)) then false else inc4_add4_fulladder_halfadder_xor_aux__476(n))  *)
  let inc4_add4_fulladder_halfadder_xor_out__472_term = Term.make_ite
    (Formula.make Formula.And [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__474
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__475
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      ; Term.t_true ] ])
    (Term.t_false)
    (Term.make_app inc4_add4_fulladder_halfadder_xor_aux__476
      [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
      )
    
  in
  Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_out__472
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; inc4_add4_fulladder_halfadder_xor_out__472_term ]
let def_inc4_add4_fulladder_halfadder_xor_aux__476 n =
  (*  (inc4_add4_fulladder_halfadder_xor_aux__476(n)  ==>  (inc4_add4_fulladder_halfadder_xor_a__474(n) || inc4_add4_fulladder_halfadder_xor_b__475(n)))  &&  ((inc4_add4_fulladder_halfadder_xor_a__474(n) || inc4_add4_fulladder_halfadder_xor_b__475(n))  ==>  inc4_add4_fulladder_halfadder_xor_aux__476(n))  *)
  let inc4_add4_fulladder_halfadder_xor_aux__476_n = Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_aux__476
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
  in
  let inc4_add4_fulladder_halfadder_xor_aux__476_formula = Formula.make Formula.Or [ Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_a__474
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]; Formula.make_lit Formula.Eq [ Term.make_app inc4_add4_fulladder_halfadder_xor_b__475
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ] ]
  in
  Formula.make Formula.And [
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__476_n; inc4_add4_fulladder_halfadder_xor_aux__476_formula ];
    Formula.make Formula.Imp [ inc4_add4_fulladder_halfadder_xor_aux__476_formula; inc4_add4_fulladder_halfadder_xor_aux__476_n ]
   ]


let delta_incr n = Formula.make Formula.And [ def_cpt__58 n; def_x3__62 n; def_x2__61 n; def_x1__60 n; def_x0__59 n; def_ok__57 n; def_aux__64 n; def_int_of_4bits_x0__89 n; def_int_of_4bits_x1__87 n; def_int_of_4bits_x2__85 n; def_int_of_4bits_x3__83 n; def_int_of_4bits_out__69 n; def_int_of_4bits_int_of_bit_x__82 n; def_int_of_4bits_int_of_bit_out__81 n; def_int_of_4bits_int_of_bit_x__84 n; def_int_of_4bits_int_of_bit_out__80 n; def_int_of_4bits_int_of_bit_x__86 n; def_int_of_4bits_int_of_bit_out__79 n; def_int_of_4bits_int_of_bit_x__88 n; def_int_of_4bits_int_of_bit_out__78 n; def_inc4_x0__353 n; def_inc4_x1__355 n; def_inc4_x2__357 n; def_inc4_x3__359 n; def_inc4_out3__68 n; def_inc4_out2__67 n; def_inc4_out1__66 n; def_inc4_out0__65 n; def_inc4_add4_a0__352 n; def_inc4_add4_a1__354 n; def_inc4_add4_a2__356 n; def_inc4_add4_a3__358 n; def_inc4_add4_b0__360 n; def_inc4_add4_b1__361 n; def_inc4_add4_b2__362 n; def_inc4_add4_b3__363 n; def_inc4_add4_c__364 n; def_inc4_add4_c0__365 n; def_inc4_add4_out0__351 n; def_inc4_add4_c1__368 n; def_inc4_add4_out1__350 n; def_inc4_add4_c2__371 n; def_inc4_add4_out2__349 n; def_inc4_add4_c3__374 n; def_inc4_add4_out3__348 n; def_inc4_add4_fulladder_a__377 n; def_inc4_add4_fulladder_b__378 n; def_inc4_add4_fulladder_c__379 n; def_inc4_add4_fulladder_c1__380 n; def_inc4_add4_fulladder_s1__382 n; def_inc4_add4_fulladder_c2__384 n; def_inc4_add4_fulladder_sum__376 n; def_inc4_add4_fulladder_carry__375 n; def_inc4_add4_fulladder_aux__387 n; def_inc4_add4_fulladder_halfadder_a__388 n; def_inc4_add4_fulladder_halfadder_b__389 n; def_inc4_add4_fulladder_halfadder_sum__386 n; def_inc4_add4_fulladder_halfadder_carry__385 n; def_inc4_add4_fulladder_halfadder_aux__391 n; def_inc4_add4_fulladder_halfadder_xor_a__392 n; def_inc4_add4_fulladder_halfadder_xor_b__393 n; def_inc4_add4_fulladder_halfadder_xor_out__390 n; def_inc4_add4_fulladder_halfadder_xor_aux__394 n; def_inc4_add4_fulladder_halfadder_a__395 n; def_inc4_add4_fulladder_halfadder_b__396 n; def_inc4_add4_fulladder_halfadder_sum__383 n; def_inc4_add4_fulladder_halfadder_carry__381 n; def_inc4_add4_fulladder_halfadder_aux__398 n; def_inc4_add4_fulladder_halfadder_xor_a__399 n; def_inc4_add4_fulladder_halfadder_xor_b__400 n; def_inc4_add4_fulladder_halfadder_xor_out__397 n; def_inc4_add4_fulladder_halfadder_xor_aux__401 n; def_inc4_add4_fulladder_a__402 n; def_inc4_add4_fulladder_b__403 n; def_inc4_add4_fulladder_c__404 n; def_inc4_add4_fulladder_c1__405 n; def_inc4_add4_fulladder_s1__407 n; def_inc4_add4_fulladder_c2__409 n; def_inc4_add4_fulladder_sum__373 n; def_inc4_add4_fulladder_carry__372 n; def_inc4_add4_fulladder_aux__412 n; def_inc4_add4_fulladder_halfadder_a__413 n; def_inc4_add4_fulladder_halfadder_b__414 n; def_inc4_add4_fulladder_halfadder_sum__411 n; def_inc4_add4_fulladder_halfadder_carry__410 n; def_inc4_add4_fulladder_halfadder_aux__416 n; def_inc4_add4_fulladder_halfadder_xor_a__417 n; def_inc4_add4_fulladder_halfadder_xor_b__418 n; def_inc4_add4_fulladder_halfadder_xor_out__415 n; def_inc4_add4_fulladder_halfadder_xor_aux__419 n; def_inc4_add4_fulladder_halfadder_a__420 n; def_inc4_add4_fulladder_halfadder_b__421 n; def_inc4_add4_fulladder_halfadder_sum__408 n; def_inc4_add4_fulladder_halfadder_carry__406 n; def_inc4_add4_fulladder_halfadder_aux__423 n; def_inc4_add4_fulladder_halfadder_xor_a__424 n; def_inc4_add4_fulladder_halfadder_xor_b__425 n; def_inc4_add4_fulladder_halfadder_xor_out__422 n; def_inc4_add4_fulladder_halfadder_xor_aux__426 n; def_inc4_add4_fulladder_a__427 n; def_inc4_add4_fulladder_b__428 n; def_inc4_add4_fulladder_c__429 n; def_inc4_add4_fulladder_c1__430 n; def_inc4_add4_fulladder_s1__432 n; def_inc4_add4_fulladder_c2__434 n; def_inc4_add4_fulladder_sum__370 n; def_inc4_add4_fulladder_carry__369 n; def_inc4_add4_fulladder_aux__437 n; def_inc4_add4_fulladder_halfadder_a__438 n; def_inc4_add4_fulladder_halfadder_b__439 n; def_inc4_add4_fulladder_halfadder_sum__436 n; def_inc4_add4_fulladder_halfadder_carry__435 n; def_inc4_add4_fulladder_halfadder_aux__441 n; def_inc4_add4_fulladder_halfadder_xor_a__442 n; def_inc4_add4_fulladder_halfadder_xor_b__443 n; def_inc4_add4_fulladder_halfadder_xor_out__440 n; def_inc4_add4_fulladder_halfadder_xor_aux__444 n; def_inc4_add4_fulladder_halfadder_a__445 n; def_inc4_add4_fulladder_halfadder_b__446 n; def_inc4_add4_fulladder_halfadder_sum__433 n; def_inc4_add4_fulladder_halfadder_carry__431 n; def_inc4_add4_fulladder_halfadder_aux__448 n; def_inc4_add4_fulladder_halfadder_xor_a__449 n; def_inc4_add4_fulladder_halfadder_xor_b__450 n; def_inc4_add4_fulladder_halfadder_xor_out__447 n; def_inc4_add4_fulladder_halfadder_xor_aux__451 n; def_inc4_add4_fulladder_a__452 n; def_inc4_add4_fulladder_b__453 n; def_inc4_add4_fulladder_c__454 n; def_inc4_add4_fulladder_c1__455 n; def_inc4_add4_fulladder_s1__457 n; def_inc4_add4_fulladder_c2__459 n; def_inc4_add4_fulladder_sum__367 n; def_inc4_add4_fulladder_carry__366 n; def_inc4_add4_fulladder_aux__462 n; def_inc4_add4_fulladder_halfadder_a__463 n; def_inc4_add4_fulladder_halfadder_b__464 n; def_inc4_add4_fulladder_halfadder_sum__461 n; def_inc4_add4_fulladder_halfadder_carry__460 n; def_inc4_add4_fulladder_halfadder_aux__466 n; def_inc4_add4_fulladder_halfadder_xor_a__467 n; def_inc4_add4_fulladder_halfadder_xor_b__468 n; def_inc4_add4_fulladder_halfadder_xor_out__465 n; def_inc4_add4_fulladder_halfadder_xor_aux__469 n; def_inc4_add4_fulladder_halfadder_a__470 n; def_inc4_add4_fulladder_halfadder_b__471 n; def_inc4_add4_fulladder_halfadder_sum__458 n; def_inc4_add4_fulladder_halfadder_carry__456 n; def_inc4_add4_fulladder_halfadder_aux__473 n; def_inc4_add4_fulladder_halfadder_xor_a__474 n; def_inc4_add4_fulladder_halfadder_xor_b__475 n; def_inc4_add4_fulladder_halfadder_xor_out__472 n; def_inc4_add4_fulladder_halfadder_xor_aux__476 n ]
let p_incr n = Formula.make_lit Formula.Eq [ Term.make_app ok__57
    [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 0)) ]
    ; Term.t_true ]
let main () = kind delta_incr p_incr

