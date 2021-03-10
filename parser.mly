
/* Parseur pour le compilateur C */

%{

  open Parsing
  open Ptree

  (* Construction d'expressions et d'instructions localis�es *)

%}

%token <string> IDENT
%token <int32> INTEGER

/* Mots cl�s */

%token IF ELSE WHILE RETURN
%token INT STRUCT SIZEOF

/* Symboles */

%token LPAR RPAR LBRACE RBRACE
%token SEMICOLON COMMA ARROW
%token EOF

/* Op�rateurs */

%token EQ
%token VERTICALBARVERTICALBAR
%token AMPERSANDAMPERSAND
%token <Ptree.binop> EQOP
%token <Ptree.binop> COMP
%token PLUS MINUS
%token STAR SLASH
%token BANG

/*s Pr�c�dences */

%nonassoc prec_then
%nonassoc ELSE

%right EQ
%left VERTICALBARVERTICALBAR /* || */
%left AMPERSANDAMPERSAND     /* && */
%left EQOP                   /* == != */
%left COMP                   /* < <= > >= */
%left PLUS MINUS             /* + - */
%left STAR SLASH             /* * /  */
%right uminus BANG           /* - ! */
%left ARROW

/*s Point d'entr�e */

%start file
%type <Ptree.file> file

%%

file:
| dl = list(decl) EOF  { dl }
;

decl:
| STRUCT s = ident LBRACE fl = list(terminated(decl_var_opt, SEMICOLON)) RBRACE SEMICOLON
    { Dstruct (s, List.flatten fl) }
| f = decl_fun
    { Dfun f }
;

decl_var_opt:
| /*LONG*/ INT vl = separated_nonempty_list(COMMA, ident)
    { List.map (fun x -> (Tint, x)) vl }
| STRUCT s = ident vl = separated_nonempty_list(COMMA, star_ident)
    { let ty = Tstructp s in List.map (fun x -> (ty, x)) vl }
;

star_ident:
| STAR id = ident { id }
;

decl_fun:
| f = formal LPAR fl = formals RPAR body = block
    { let ty, id = f in
      { fun_typ = ty;
	fun_name = id;
	fun_formals = fl;
	fun_body = body; } }
;

formals:
| f = separated_list(COMMA, formal) { f }
;

formal:
| /*LONG*/ INT          id = ident { Tint,       id }
| STRUCT s = ident STAR id = ident { Tstructp s, id }
;

lvalue:
| ident
    { Lident $1 }
| expr ARROW ident
    { Larrow ($1, $3) }
;

expr:
  e = expr_node
  { { expr_node = e; expr_loc = $startpos, $endpos } }
;

expr_node:
| lvalue
    { Eright $1 }
| lvalue EQ expr
    { Eassign ($1, $3) }
| expr VERTICALBARVERTICALBAR expr
    { Ebinop (Bor, $1, $3) }
| expr AMPERSANDAMPERSAND expr
    { Ebinop (Band, $1, $3) }
| expr EQOP expr
    { Ebinop ($2, $1, $3) }
| expr COMP expr
    { Ebinop ($2, $1, $3) }
| expr PLUS expr
    { Ebinop (Badd, $1, $3) }
| expr MINUS expr
    { Ebinop (Bsub, $1, $3) }
| expr STAR expr
    { Ebinop (Bmul, $1, $3) }
| expr SLASH expr
    { Ebinop (Bdiv, $1, $3) }
| MINUS expr %prec uminus
    { Eunop (Uminus, $2) }
| BANG expr
    { Eunop (Unot, $2) }
| INTEGER
    { Econst $1 }
| id = ident LPAR el = separated_list(COMMA, expr) RPAR
    { Ecall (id, el) }
| LPAR expr RPAR
    { $2.expr_node }
| SIZEOF LPAR STRUCT id = ident RPAR
    { Esizeof id }
;

stmt:
  s = stmt_node
   { { stmt_node = s; stmt_loc = $startpos, $endpos } }
;

stmt_node:
| SEMICOLON
   { Sskip }
| expr SEMICOLON
   { Sexpr $1 }
| vl = decl_var_opt SEMICOLON
   { Sdecl vl }
| vl = decl_var_opt EQ expr SEMICOLON
   { Sinit (vl,$3) }
| IF LPAR expr RPAR stmt %prec prec_then
   { Sif ($3, $5, { stmt_node = Sskip; stmt_loc = $startpos, $endpos }) }
| IF LPAR expr RPAR stmt ELSE stmt
   { Sif ($3, $5, $7) }
| WHILE LPAR expr RPAR stmt
   { Swhile ($3, $5) }
| block
   { Sblock $1 }
| RETURN expr SEMICOLON
   { Sreturn $2 }
;


block:
| LBRACE sl = list(stmt) RBRACE { sl }
;


ident:
| id = IDENT { { id = id; id_loc = $startpos, $endpos } }
;
