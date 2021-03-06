%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT
%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */

/* Added tokens */
%token TBOOL    /* bool */
%token LSHIFT   /* << */
%token RSHIFT   /* >> */
%token URSHIFT  /* >>> */
%token LESS     /* < */
%token LESSEQ   /* <= */
%token GREAT    /* > */
%token GREATEQ  /* >= */
%token NOTEQ    /* != */
%token AND      /* & */
%token OR       /* | */
%token BAND     /* [&] */
%token BOR      /* [|] */
%token TRUE
%token FALSE
%token NEW      /* new */
%token FOR      /* for */

%left BAND BOR
%left OR
%left AND                                  
%left EQEQ NOTEQ                                 
%left LESS LESSEQ GREAT GREATEQ
%left LSHIFT RSHIFT URSHIFT
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
/* STUBWITH */

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | rtyp=ty name=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { rtyp; name; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TVOID  { TVoid }
  | TINT   { TInt }
    | TBOOL  { TBool }
  | r=rtyp { TRef r }

rtyp:
  | TSTRING { RString }
  /*| t=ty LBRACKET RBRACKET { RArray t }*/ 

%inline bop:
  | STAR   { Mul }
    | PLUS   { Add }
  | DASH   { Sub }
    | LSHIFT { Shl }
    | RSHIFT { Shr }
    | URSHIFT { Sar}
    | LESS   { Lt }
    | LESSEQ { Lte }
    | GREAT  { Gt }
    | GREATEQ { Gte }
    | NOTEQ  { Neq }
    | AND        { And }
    | OR         { Or }
    | BAND   { IAnd }
    | BOR        { IOr }
  | EQEQ   { Eq } 

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=ty NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT      { loc $startpos $endpos @@ CInt i }
	| s=STRING	 { loc $startpos $endpos @@ CStr s }
  | b=TRUE     { loc $startpos $endpos @@ CBool true }
  | b=FALSE    { loc $startpos $endpos @@ CBool false }
	| t=ty LBRACKET RBRACKET g=list(gexp) {loc $startpos $endpos @@  CArr (t, g)}

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
exp:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | i=INT               { loc $startpos $endpos @@ CInt i }
    | s=STRING                      { loc $startpos $endpos @@ CStr s } 
  | t=ty NULL           { loc $startpos $endpos @@ CNull t }
  | b=TRUE       { loc $startpos $endpos @@ CBool true}
  | b=FALSE         { loc $startpos $endpos @@ CBool false}  
	| id=IDENT LPAREN elist=list(exp) RPAREN
												{ loc $startpos $endpos @@ Call (id, elist) }
	| NEW t=ty LBRACKET RBRACKET elist=list(exp)
												{ loc $startpos $endpos @@ CArr (t, elist) }			/* double check */
	| NEW t=ty LBRACKET i=exp RBRACKET
												{ loc $startpos $endpos @@ NewArr (t, i) }						/* double check */
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | id=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (id,es) }
  | LPAREN e=exp RPAREN { e } 

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | id=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (id, es) }
  | ifs=if_stmt         { ifs }
    | FOR LPAREN v=separated_list(COMMA, vdecl) SEMI e=exp SEMI s=stmt RPAREN b=block
                                                { loc $startpos $endpos @@ For(v, Some e, Some s, b) }          /* double check */
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }