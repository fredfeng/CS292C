open Base
open Lang

(** Convert a memory read of a [path] to a combination of [Var] and [Select] *)
let read_from_path (p : path) : aexp =
  match p with
  | { var; indices = [] } -> Var var
  | _ -> Todo.at_level 2 ~msg:"read_from_path"

(** Convert an assignment to a [path] to a variable assignment
    using [Select] and [Store]. *)
let write_to_path (lhs : path) (rhs : aexp) : stmt =
  match lhs with
  | { var; indices = [] } -> Assign { lhs = var; rhs }
  | _ -> Todo.at_level 2 ~msg:"write_to_path"
