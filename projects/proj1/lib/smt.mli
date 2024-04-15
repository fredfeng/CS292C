type status = Valid | Invalid of string | Unknown
type env = (string, Z3.Expr.expr) Base.List.Assoc.t

val int_sort : Z3.Sort.sort
val arr_sort : Z3.Sort.sort -> Z3.Sort.sort
val sort_of_ty : Lang.ty -> Z3.Sort.sort
val aexp : env -> Lang.aexp -> Z3.Expr.expr
val formula : env -> Lang.formula -> Z3.Expr.expr
val convert : string * Lang.ty -> string * Z3.Expr.expr
val check_validity : Lang.gamma -> Lang.formula -> status
