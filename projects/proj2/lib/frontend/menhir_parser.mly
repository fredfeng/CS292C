(* tokens *)
%token EOF
%token P CNF MINUS ZERO PERCENT
%token <int> NUM

(* start symbol *)
%start <Description.t> description

%%

description:
  | info = info; f = formula; option(satlib_eof); EOF 
    { Description.{ 
        num_vars = fst info; 
        num_clauses = snd info; 
        f = Formula.of_ints f
      } 
    }

satlib_eof:
  | PERCENT; ZERO
    { () }
  | ZERO
    { () }

nat:
  | n = NUM
    { n }
  | ZERO
    { 0 }

info:
  | P; CNF; nbvar = nat; nbclauses = nat
    { (nbvar, nbclauses) }

formula:
  | 
    { [] }
  | c = clause; f = formula
    { c :: f }

clause:
  | ls = nonempty_list(literal); ZERO
    { ls }

literal:
  | MINUS; n = NUM
    { (-n) }
  | n = NUM
    { n }

%%