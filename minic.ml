
(* Fichier principal du compilateur mini-c *)

open Format
open Lexing

let () = Printexc.record_backtrace true

let parse_only = ref false
let type_only = ref false
let interp_rtl = ref false
let interp_ertl = ref false
let interp_ltl = ref false
let interp_asm = ref false
let debug = ref false
let life_cycle = ref false
let interferences = ref false
let colorize = ref false

let ifile = ref ""

let set_file f s = f := s

let options =
  ["--parse-only", Arg.Set parse_only,
     "  stops after parsing";
   "--type-only", Arg.Set type_only,
     "  stops after typing";
   "--interp-rtl", Arg.Set interp_rtl,
     "  interprets RTL (and does not compile)";
   "--interp-ertl", Arg.Set interp_ertl,
     "  interprets ERTL (and does not compile)";
   "--interp-ltl", Arg.Set interp_ltl,
     "  interprets LTL (and does not compile)";
   "--interp-asm", Arg.Set interp_asm,
     "  interprets asm";
   "--debug", Arg.Set debug,
     "  debug mode";
   "--life-cycle", Arg.Set life_cycle,
     "  show life cycle";
   "--interferences", Arg.Set interferences,
     "  show interferences";
   "--colorize", Arg.Set colorize,
     "  show colorization"
   ]

let usage = "usage: mini-c [options] file.c"

let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
  Arg.parse options (set_file ifile) usage;
  if !ifile="" then begin eprintf "missing file\n@?"; exit 1 end;
  if not (Filename.check_suffix !ifile ".c") then begin
    eprintf "file must have extension .c\n@?";
    Arg.usage options usage;
    exit 1
  end;
  let debug = !debug in
  let f = open_in !ifile in
  let buf = Lexing.from_channel f in
  try
    let p = Parser.file Lexer.token buf in
    close_in f;
    if !parse_only then exit 0;
    let p = Typing.program p in
    if !type_only then exit 0;
    let p = Rtl.program p in
    if debug then Rtltree.print_file std_formatter p;
    if !interp_rtl then begin ignore (Rtlinterp.program p); exit 0 end;
    let p = Ertl.program p in
    if debug then Ertltree.print_file std_formatter p;
    if !interp_ertl then begin ignore (Ertlinterp.program p); exit 0 end;
    if !life_cycle then begin ignore (Liveness.program p); exit 0 end;
    if !interferences then begin ignore (Interference.program p); exit 0 end;
    if !colorize then begin ignore (Colorize.program p); exit 0 end;
    let p = Ltl.program p in
    if debug then Ltltree.print_file std_formatter p;
    if !interp_ltl then begin ignore (Ltlinterp.program p); exit 0 end;
    let p = Linearize.program p in
    if debug then X86_64.print_program std_formatter p;
    let file_s = (Filename.chop_suffix !ifile ".c")^".s" in
    X86_64.print_in_file ~file:file_s p; exit 0
  with
    | Lexer.Lexical_error c ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "lexical error: %s@." c;
	exit 1
    | Parser.Error ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "syntax error@.";
	exit 1
    | Typing.Error s->
	eprintf "File \"%s\", %s@." !ifile s;
	exit 1
    | e ->
        let bt = Printexc.get_backtrace () in
        eprintf "anomaly: %s\n@." (Printexc.to_string e);
        eprintf "%s@." bt;
	exit 2





