
(* Analyse lexicale *)

{

  open Lexing
  open Parser
  open Ptree

  (* Erreurs lexicales *)

  exception Lexical_error of string

  let id_or_keyword =
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [ "int", INT; "struct", STRUCT;
	"if", IF; "else", ELSE; "while", WHILE;
	"return", RETURN;
	"sizeof", SIZEOF; ];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum;
        pos_cnum=0 }

  let char_error s = raise (Lexical_error ("illegal character sequence: " ^ s))

  let decode_char s = match String.length s with
    | 1 -> Char.code s.[0]
    | 2 | 4 when s.[0] == '\\' ->
      begin match s.[1] with
        | 'n' -> 10 (* Char.code '\n' *)
        | 't' -> 9  (* Char.code '\t' *)
        | '\'' -> 39 (* Char.code '\'' *)
        | '\"' -> 34 (* Char.code '\"' *)
        | 'x' -> int_of_string ("0x" ^ String.sub s 2 2)
        | _ -> char_error s
      end
    | _ -> char_error s

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = (alpha | '_') (alpha | '_' | digit)*
let octal = ['0'-'7']
let hexa = digit | ['a'-'f' 'A'-'F']
let char =
  [^'\000'-'\x1f' '\\' '\'' '\"']
  | '\\' ('n' | 't' | '\'' |'\"')
  | "\\x" hexa hexa

rule token = parse
  | '\n'
      { newline lexbuf; token lexbuf }
  | [' ' '\t' '\r']+
      { token lexbuf }
  | "/*"
      { comment lexbuf; token lexbuf }
  | "//" [^'\n']* ('\n' | eof)
      { newline lexbuf; token lexbuf }
  | ident as s
      { id_or_keyword s }
  | "0"
      { INTEGER 0l }
  | (['1'-'9'] digit*) as s
      { try
	  INTEGER (Int32.of_string s)
	with _ ->
	  raise (Lexical_error ("invalid integer constant '" ^ s ^ "'")) }
  | "0" (octal+ as s)
      { try
	  INTEGER (Int32.of_string ("0o" ^ s))
	with _ ->
	  raise (Lexical_error ("invalid octal constant '" ^ s ^ "'")) }
  | ("0x" hexa+) as s
      { try
	  INTEGER (Int32.of_string s)
	with _ ->
	  raise (Lexical_error ("invalid hexadecimal constant '" ^ s ^ "'")) }
  | '\'' (char as s) '\''
      { INTEGER (Int32.of_int (decode_char s)) }
  | '{'
      { LBRACE }
  | '}'
      { RBRACE }
  | '('
      { LPAR }
  | ')'
      { RPAR }
  | ','
      { COMMA }
  | ';'
      { SEMICOLON }
  | "->"
      { ARROW }
  | "-"
      { MINUS }
  | "+"
      { PLUS }
  | "*"
      { STAR }
  | "/"
      { SLASH }
  | "!"
      { BANG }
  | "&&"
      { AMPERSANDAMPERSAND }
  | "||"
      { VERTICALBARVERTICALBAR }
  | "="
      { EQ }
  | ">"
      { COMP Bgt }
  | ">="
      { COMP Bge }
  | "<"
      { COMP Blt }
  | "<="
      { COMP Ble }
  | "=="
      { EQOP Beq }
  | "!="
      { EQOP Bneq }
  | _
      { raise (Lexical_error ("illegal character: " ^ lexeme lexbuf)) }
  | eof
      { EOF }

and comment = parse
  | "*/" { () }
  | '\n' { newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise (Lexical_error "unterminated comment") }

