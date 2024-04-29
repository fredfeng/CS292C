(** Davis-Putnam-Logemann-Loveland (DPLL) solver *)

open Base

exception Solver_error

(* Make a solver given a CNF problem description *)
module Make (Problem : sig
  val desc : Description.t
end) =
struct
  (* the set of all variables *)
  let vars = Formula.vars Problem.desc.f

  (* the number of variables *)
  let num_vars = Set.length vars

  (* all clauses in the CNF problem *)
  let cs : Formula.t = Problem.desc.f

  (** Construct a resolution proof of the current (partial) decision assignment *)
  let make_proof (a : Assign.t) (unsat : Clause.t) : Proof.t =
    Todo.part 4 "Dpll.make_proof" ~dummy:(Proof.fact unsat)

  exception Backtrack of Proof.t

  let rec solve (s : State.t) : State.t =
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    Logs.debug (fun m -> m "State: %a" State.pp s);
    let r, a = Bcp.run s.level s.a cs in
    (* update assignment in the solver state  *)
    let s = { s with a } in
    match r with
    | Sat ->
        Logs.debug (fun m -> m "BCP: SAT");
        s
    | Unsat c ->
        Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c);
        let proof = make_proof s.a c in
        Logs.debug (fun m -> m "Backtracking...");
        raise (Backtrack proof)
    | Unknown -> (
        Logs.debug (fun m -> m "BCP: Unknown");
        (* pick (opposite) decision literals for the left & the right
           branches of the decision tree *)
        let left =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
          Heuristics.random_unassigned vars s.a
          |> Option.value_exn ~error:(Error.of_string "No unassigned variable")
        in
        let right = Lit.negate left in
        try
          (* decide [left] and solve *)
          Logs.info (fun m -> m "Deciding %a" Lit.pp left);
          solve (State.decide s left)
        with Backtrack left_proof ->
          Todo.part 1 "Dpll.solve: left branch unsat")

  (** Solving result *)
  let result : Solution.t =
    try
      let s' = solve State.init in
      SATISFIABLE s'.a.nu
    with Backtrack proof ->
      (* backtracked to the initial level, so unsat overall *)
      Logs.debug (fun m -> m "Backtracked to the initial level");
      UNSATISFIABLE (Script.make [] proof)
end

(** Run DPLL algorithm *)
let run (desc : Description.t) : Solution.t =
  (* create a solver module and run the solver *)
  let module Solver = Make (struct
    let desc = desc
  end) in
  (* get the solver result *)
  Solution.verify desc Solver.result;
  Solver.result
