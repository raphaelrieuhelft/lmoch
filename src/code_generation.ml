open Asttypes
open Aez_ast
open Format

let str_base_type = function
  | Tbool -> "Type.type_bool"
  | Tint -> "Type.type_int"
  | Treal -> "Type.type_float"

let pp_ident = Ident.print  

let generate_declare_symbol ff decl =
  fprintf ff "let %a = declare_symbol \"%a\" [ Type.type_int ] %s@." pp_ident decl.sd_ident pp_ident decl.sd_ident (str_base_type decl.sd_type)

let generate_declare_symbols ff =
  List.iter (generate_declare_symbol ff)

let main decls out_id =
  let ff = std_formatter in
  generate_declare_symbols ff decls;
  Format.fprintf ff "@."