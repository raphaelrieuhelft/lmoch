type constant = Asttypes.const

type term_operator = TO_plus | TO_minus | TO_times | TO_div | TO_mod

type comparison = Cmp_eq | Cmp_neq | Cmp_lt | Cmp_leq

type logic_connector = LC_and | LC_or | LC_impl | LC_not

type ident = Ident.t


type term =
  | T_cst of constant
  | T_op of term_operator * term * term
  | T_ite of formula * term * term
  | T_app of ident * int (* T_app(id,k) represents the call id(n-k) where n is the global term representing the time *)
  
  (* intermediate compilation, not present in final form *)
  | T_formula of formula
  | T_tuple of term list
  | T_app_node of ident * int * (term list)
  
  
and formula =
  | F_term of term
  | F_cmp of comparison * term * term
  | F_time_eq of int (* F_time_eq(k) represents the formula "n = k" where n is the global term representing the time *)
  | F_lco of logic_connector * (formula list)

  
type stream_body = SB_term of term | SB_formula of formula

type stream_declaration = { 
  sd_ident: ident;
  sd_type: Asttypes.base_ty;
  sd_body: stream_body
}


type node = stream_declaration list