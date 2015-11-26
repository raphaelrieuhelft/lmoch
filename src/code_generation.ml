open Ident
open Asttypes
open Aez_ast

let spf = Format.sprintf

let str_ident ident = spf "%s__%i" ident.name ident.id

let str_base_type = function
  | Tbool -> "Type.type_bool"
  | Tint -> "Type.type_int"
  | Treal -> "Type.type_float"

let generate_declare_symbol push decl =
  let s_id = str_ident decl.sd_ident in
  push (spf "let %s = declare_symbol \"%s\" [ Type.type_int ] %s@." s_id s_id (str_base_type decl.sd_type))

let generate_declare_symbols push =
  List.iter (generate_declare_symbol push)
  
  
let main decls out_id =
  generate_declare_symbols (Format.printf "%s") decls;
  Format.printf "@."