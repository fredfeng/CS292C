(** Solver state *)

open Base

type t = {
  level : int;
  decision : Lit.t option;
  a : Assign.t;
  h : Heuristics.t;
}
[@@deriving show]

let invariant n (s : t) : unit = Assign.invariant n ~level:s.level s.a
let init_level = 0

(** Initial state *)
let init : t =
  {
    level = init_level;
    decision = Some Lit.dummy;
    a = Assign.assign_decision Assign.empty 0 Lit.dummy;
    h = Heuristics.empty ();
  }

let decide (s : t) (l : Lit.t) : t =
  {
    s with
    level = s.level + 1;
    decision = Some l;
    a = Assign.assign_decision s.a (s.level + 1) l;
  }
