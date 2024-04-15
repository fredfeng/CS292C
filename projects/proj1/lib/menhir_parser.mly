
%{
  (* consecutive comparisons *)
  type comps = Lang.aexp * (Lang.comp * Lang.aexp) list

  (* convert consecutive comparisons to either bexp or fomula *)
  let comps_to f fc fb (e1, l) =
    Base.List.fold_left l
      ~init:(e1, fb)
      ~f:(fun (prev_e, b) (op, e) -> 
          (e, f (b, fc (op, prev_e, e)))) |> snd
  let comps_to_bexp : comps -> Lang.bexp = 
    comps_to 
      (fun (b1, b2) : Lang.bexp -> 
        match b1 with Lang.Bool true -> b2 | _ -> Lang.And (b1, b2)) 
      (fun (op, e1, e2) -> Lang.Comp (op, e1, e2))
      (Lang.Bool true)
  let comps_to_formula : comps -> Lang.formula = 
    comps_to 
      (fun (f1, f2) -> 
        match f1 with Lang.FBool true -> f2 | _ -> Lang.FConn (Lang.And, f1, f2))
      (fun (op, e1, e2) -> Lang.FComp (op, e1, e2))
      (Lang.FBool true)
%}

(* tokens *)
%token EOF LPAR RPAR LBRAC RBRAC
%token PLUS MINUS TIMES DIV MOD
%token EQ NEQ LT LEQ GT GEQ
%token NOT AND OR IMPLY IFF
%token TRUE FALSE
%token FORALL EXISTS COLON
%token ASSIGN IF ELSE WHILE INVARIANT PRINT
%token SEMI COMMA LCURLY RCURLY
%token ASSUMES ASSERTS
%token METHOD VAR REQUIRES ENSURES RET RETURNS
%token TINT TARRAY
%token <string> ID
%token <int> NUM

(* start symbol *)
%start <Lang.aexp> aexp_eof
%start <Lang.bexp> bexp_eof
%start <Lang.path> path_eof
%start <Lang.formula> formula_eof
%start <Lang.stmt> stmt_eof
%start <Lang.meth> meth_eof
%start <Lang.prog> prog_eof

(* precedence *)
%nonassoc QUANT
%right IMPLY IFF
%left OR
%left AND
%nonassoc NOT
%left PLUS MINUS
%nonassoc UMINUS
%left TIMES DIV MOD

%%

aexp_eof:
  | e=aexp; EOF { e }
  ;

aexp:
  | n=NUM 
    { Lang.Int n }
  | p=path;
    { Desugar.read_from_path p }
  | LPAR; e=aexp; RPAR 
    { e }
  | MINUS; e=aexp %prec UMINUS 
    { Lang.Aop (Sub, Lang.Int 0, e) }
  | e1=aexp; PLUS; e2=aexp 
    { Lang.Aop (Add, e1, e2) }
  | e1=aexp; MINUS; e2=aexp 
    { Lang.Aop (Sub, e1, e2) }
  | e1=aexp; TIMES; e2=aexp 
    { Lang.Aop (Mul, e1, e2) }
  | e1=aexp; DIV; e2=aexp 
    { Lang.Aop (Div, e1, e2) }
  | e1=aexp; MOD; e2=aexp 
    { Lang.Aop (Mod, e1, e2) }
  ;

path_eof:
  | a=path; EOF { a }
  ;

path0:
  | x=ID
    { (x, []) }
  | p=path0; LBRAC; e=aexp; RBRAC
    { let (x, es) = p in (x, e::es) }
  ;

path:
  | p=path0
    { let (x, es) = p in Lang.{ var = x; indices = List.rev es} }
  ;

comp_op:
  | EQ
    { Lang.Eq }
  | NEQ
    { Lang.Neq }
  | LT
    { Lang.Lt }
  | LEQ
    { Lang.Leq }
  | GT
    { Lang.Gt }
  | GEQ
    { Lang.Geq }
  ;

comps:
  | e1=aexp; l=nonempty_list(pair(comp_op, aexp))
    { (e1, l) : comps }
  ;

bexp_eof:
  | b=bexp; EOF { b }
  ;

bexp:
  | c=comps
    { comps_to_bexp c }
  | TRUE 
    { Lang.Bool true }
  | FALSE 
    { Lang.Bool false }
  | NOT; b=bexp 
    { Lang.Not b }
  | b1=bexp; AND; b2=bexp 
    { Lang.And (b1, b2) }
  | b1=bexp; OR; b2=bexp 
    { Lang.Or (b1, b2) }
  | LPAR; b=bexp; RPAR 
    { b }
  ;


quantifier:
  | FORALL
    { Lang.Forall }
  | EXISTS 
    { Lang.Exists }
  ;

formula_eof:
  | f=formula; EOF 
    { f }
  ;

formula:
  | c=comps
    { comps_to_formula c }
  | TRUE 
    { Lang.FBool true }
  | FALSE 
    { Lang.FBool false }
  | LPAR; f=formula; RPAR
    { f }
  | q=quantifier; x=ID; COLON; COLON; f=formula %prec QUANT
    { Lang.FQ (q, x, f) }
  | NOT; b=formula 
    { Lang.FNot b }
  | b1=formula; AND; b2=formula 
    { Lang.FConn (And, b1, b2) }
  | b1=formula; OR; b2=formula 
    { Lang.FConn (Or, b1, b2) }
  | b1=formula; IMPLY; b2=formula 
    { Lang.FConn (Imply, b1, b2) }
  | b1=formula; IFF; b2=formula 
    { Lang.FConn (Iff, b1, b2) }
  ;


stmt_eof:
  | c=stmt; EOF { c }
  ;

stmt:
  | lhs=path; ASSIGN; rhs=aexp; SEMI
    { Desugar.write_to_path lhs rhs }
  | WHILE; cond=bexp; inv=list(inv); body=block
    { Lang.While { cond; inv; body } }
  | IF; cond=bexp; thn=block; ELSE; els=block
    { Lang.If { cond; thn; els } }
  | ASSUMES; f=formula; SEMI
    { Lang.Assume f }
  | ASSERTS; f=formula; SEMI
    { Lang.Assert f }
  | lhs=path; ASSIGN; TIMES; SEMI
    { Lang.Havoc (Lang.var_of_path lhs) }
  | PRINT; a=aexp; SEMI
    { Lang.Print a }
  | lhs=path; ASSIGN; callee=ID; LPAR; args=separated_list(COMMA, aexp); RPAR; SEMI
    { Lang.Call { lhs = Lang.var_of_path lhs; callee; args } }
  ;

inv:
  | INVARIANT; inv=formula
    { inv }
  ;

block:
  | LCURLY; stmts=list(stmt); RCURLY
    { stmts }
  ;

meth_eof:
  | p=meth; EOF { p }
  ;

requires:
  | REQUIRES; f=formula
    { f }
  ;

ensures:
  | ENSURES; f=formula
    { f }
  ;

param:
  | x=ID; COLON; t=ty
    { (x, t) }
  ;

params:
  | l=separated_list(COMMA, param)
    { l }
  ;

returns:
  | RETURNS; LPAR; x=ID; COLON; t=ty; RPAR
    { (x, t) }

ret:
  | RET; e=aexp; SEMI
    { e }

meth:
  | METHOD; id=ID; LPAR; params=params; RPAR;
    returns = returns;
    requires=list(requires);
    ensures=list(ensures);
    LCURLY;
    locals=list(local);
    body=list(stmt);
    ret=ret;
    RCURLY
    { { id; params; returns; requires; ensures; locals; body; ret } }
  ;

ty:
  | TINT
    { Lang.TInt }
  | TARRAY; LT; t=ty; GT
    { Lang.TArr t }

local:
  | VAR; id=ID; COLON; t=ty; SEMI
    { ( id, t ) }

prog_eof:
  | p=prog; EOF { p }
  ;

prog:
  | l=list(meth)
    { l }
  ;

%%
