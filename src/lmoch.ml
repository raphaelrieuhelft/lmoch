
(* Programme principal *)

open Format
open Lexing
open Lexer
open Parser
open Parse_ast

let usage = "usage: "^Sys.argv.(0)^" [options] file.lus main"

let parse_only = ref false
let type_only = ref false
let norm_only = ref false
let lucy_printer = ref false
let ocaml_printer = ref true
let verbose = ref false
let run_proof = ref false

let spec =
  ["-parse-only", Arg.Set parse_only, "  stops after parsing";
   "-type-only", Arg.Set type_only, "  stops after typing";
   "-norm-only", Arg.Set norm_only, "  stops after normalization";
   "-verbose", Arg.Set verbose, "print intermediate transformations";
   "-v", Arg.Set verbose, "print intermediate transformations";
   "-run-proof", Arg.Set run_proof, "runs the computed proof immediately";
   "-no-max-depth",  Arg.Set Code_generation.no_max_depth, "no max depth optimisation";
  ]

let file, main_node =
  let file = ref None in
  let main = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".lus") then
      raise (Arg.Bad "no .lus extension");
    file := Some s
  in
  let set_main s =
    main := Some s
  in
  let cpt = ref 0 in
  let set s =
    incr cpt;
    match !cpt with
    | 1 -> set_file s
    | 2 -> set_main s
    | _ -> raise (Arg.Bad "Too many arguments")
  in
  Arg.parse spec set usage;
  (match !file with Some f -> f | None -> Arg.usage spec usage; exit 1),
  (match !main with Some n -> n | None -> Format.printf "No main node specified: set to \"check\" by default.@.@."; "check")

let report_loc (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.token lb in
    close_in c;
    if !parse_only then exit 0;
    let ft = Typing.type_file f main_node in
    if !verbose then begin
      Format.printf "/**************************************/@.";
      Format.printf "/* Typed ast                          */@.";
      Format.printf "/**************************************/@.";
      Typed_ast_printer.print_node_list_std ft
    end;
    if !type_only then exit 0;
    if main_node = "" then exit 0;

	
	
	let decls, input_tvars, output_id = Compile_to_aez.main ft main_node in
	if !verbose then begin
      Format.printf "/**************************************/@.";
      Format.printf "/* AEZ formulas                       */@.";
      Format.printf "/**************************************/@.";
	  Aez_printer.main decls input_tvars output_id;
	end;

	let proof_dir = "../proofs" in 
	let proof_fname = (Filename.chop_suffix (Filename.basename file) ".lus")^("_"^main_node)^("_proof.ml") in
	let proof_path = proof_dir^"/"^proof_fname in
	let () = Code_generation.main proof_path decls input_tvars output_id in
	Format.printf "Proof written in %s@." proof_path;
	
	
	(if !run_proof then begin
		Format.printf "Running proof...@.@.";
		let target_fname = (Filename.chop_suffix proof_fname ".ml")^(".byte") in
		ignore (Unix.system ("cp "^proof_path ^" "^proof_fname));
		let command = "ocamlbuild -no-links -classic-display -libs \"unix,nums,aez\" -cflags \"-I ../../lib/aez-0.3\" -lflags \"-I ../../lib/aez-0.3\" -tags \"debug,annot\" "^target_fname in
		ignore (Unix.system command);
		ignore (Unix.system ("ocamlrun "^("_build/"^target_fname)));
		ignore (Unix.system ("rm "^proof_fname))
	end
    else 
    Format.printf "Compile and run this file or use -run-proof option for results.@.");

    exit 0
  with
    | Lexical_error s ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "lexical error: %s\n@." s;
	exit 1
    | Parsing.Parse_error ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "syntax error\n@.";
	exit 1
    | Typing.Error(l,e) ->
	report_loc l;
	eprintf "%a\n@." Typing.report e;
	exit 1
    | e ->
        eprintf "Anomaly: %s\n@." (Printexc.to_string e);
        exit 2
