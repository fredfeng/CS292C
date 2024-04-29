open Base

type t = SATISFIABLE of Eval.t | UNSATISFIABLE of Script.t

let pp : t Fmt.t =
  let open Fmt in
  fun ppf -> function
    | SATISFIABLE nu -> pf ppf "@[<v>s SATISFIABLE@ v %a 0@]" (hbox Eval.pp) nu
    | UNSATISFIABLE p -> pf ppf "@[<v>s UNSATISFIABLE@ %a@]" Script.pp p

let pp_short : t Fmt.t =
  let open Fmt in
  fun ppf -> function
    | SATISFIABLE _ -> pf ppf "s SATISFIABLE"
    | UNSATISFIABLE _ -> pf ppf "s UNSATISFIABLE"

let verify_sat (desc : Description.t) (t : t) : unit =
  match t with
  | SATISFIABLE nu ->
      if not (Eval.formula nu desc.f) then (
        Logs.err (fun m -> m "Fails to verify SATISFIABLE solution");
        failwith "verify_sat")
  | UNSATISFIABLE _ -> ()

let verify_unsat (desc : Description.t) (t : t) : unit =
  match t with
  | SATISFIABLE _ -> ()
  | UNSATISFIABLE proof ->
      let clause_set = Set.of_list (module Clause) desc.f in
      if not (Script.is_refutation clause_set proof) then (
        Logs.err (fun m -> m "Fails to verify UNSATISFIABLE proof");
        failwith "verify_unsat")

let verify (desc : Description.t) (t : t) : unit =
  verify_sat desc t;
  verify_unsat desc t

let is_sat = function SATISFIABLE _ -> true | UNSATISFIABLE _ -> false
let is_unsat = function SATISFIABLE _ -> false | UNSATISFIABLE _ -> true
