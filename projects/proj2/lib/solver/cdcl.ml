(** Conflict-driven clause learning (CDCL) solver *)

open Base

exception Solver_error

(* Make a solver given a CNF problem description *)
module Make (Problem : sig
  val desc : Description.t
end) =
struct
  (* The set of all variables *)
  let vars = Formula.vars Problem.desc.f

  (** The number of variables *)
  let num_vars = Set.length vars

  (** Restart threshold *)
  let restart_threshold = ref 1

  (** Restart increment strategy: multiply the threshold by 2 each time *)
  let restart_inc n = n * 2

  (** Restart count *)
  let restart_count = ref 0

  (** All original clauses in the CNF problem *)
  let cs : Formula.t = Problem.desc.f

  (** Set of all original clauses *)
  let cset = Set.of_list (module Clause) cs

  (** Allow the same number of conflicts as the number of original clauses. Feel
      free to change this parameter. *)
  let _CAPACITY = List.length cs

  (** A FIFO queue of capacity [_CAPACITY] to hold conflicts. When a new
      conflict is learned but the queue is at its capacity, the oldest conflict
      will be evicted. *)
  let conflicts = Queue.create ~capacity:_CAPACITY ()

  (** List of learned lemmas, each of which is a (conflict clause, proof) pair *)
  let lemmas : Script.Lemma.t list ref = ref []

  (** Learn the given conflict *)
  let learn_conflict (s : State.t) (c : Clause.t) (proof : Proof.t) : unit =
    if not (Queue.mem conflicts c ~equal:Clause.equal || Set.mem cset c) then (
      Logs.debug (fun m -> m "Learning conflict: %a" Clause.pp c);
      Heuristics.record_conflict s.h c;
      Int.incr restart_count;
      lemmas := Script.Lemma.make c proof :: !lemmas;
      while Queue.length conflicts >= _CAPACITY do
        ignore @@ Queue.dequeue_exn conflicts
      done;
      Queue.enqueue conflicts c)
    else Logs.debug (fun m -> m "Discarding conflict: %a" Clause.pp c)

  (** Return the current list of conflicts *)
  let curr_conflicts () = Queue.to_list conflicts

  (** [analyze level a unsat] analyzes the unsatisfiable clause [unsat],
      returning a conflict to learn, and a resolution proof of the conflict *)
  let analyze (level : int) (a : Assign.t) (unsat : Clause.t) :
      Clause.t * Proof.t * int =
    Logs.debug (fun m ->
        m "analyze: level = %d, unsat clause = %a" level Clause.pp unsat);
    (* retrieve the decision and the trail of implied literals *)
    let { implied; decision } : Assign.Trail.t = Assign.trail_exn a level in
    let conflict = Todo.part 2 "Cdcl.analyze: conflict" in
    let beta = Todo.part 2 "Cdcl.analyze: conflict" in
    let proof =
      Todo.part 3 "Cdcl.analyze: proof" ~dummy:(Proof.fact Clause.empty)
    in
    (conflict, proof, beta)

  exception Backtrack of int
  exception Restart

  (** [check_result ()] restarts the solver by raising [Restart] if the number
      of learned conflicts in the current run exceeds the threshold. *)
  let check_restart () : unit =
    if !restart_count >= !restart_threshold then (
      Logs.info (fun m ->
          m "Reached threshold: %d. Restarting..." !restart_threshold);
      restart_threshold := restart_inc !restart_threshold;
      restart_count := 0;
      raise Restart)

  let rec solve (s0 : State.t) : State.t =
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    Logs.debug (fun m -> m "Input state: %a" State.pp s0);
    Logs.debug (fun m -> m "Learned conflicts:");
    Logs.debug (fun m ->
        m "%a" Fmt.(vbox @@ list Clause.pp) (curr_conflicts ()));

    check_restart ();

    let r, a = Bcp.run s0.level s0.a (cs @ curr_conflicts ()) in
    (* update the assignment in the solver state *)
    let s = { s0 with a } in
    Logs.debug (fun m -> m "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
    Logs.debug (fun m -> m "State after unit-prop: %a" State.pp s);

    match r with
    | Sat ->
        Logs.debug (fun m -> m "BCP: SAT");
        s
    | Unsat c ->
        Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c);
        let c, proof, beta = analyze s.level s.a c in
        learn_conflict s c proof;
        Logs.debug (fun m -> m "Backtracking to level %d" beta);
        raise (Backtrack beta)
    | Unknown ->
        Logs.debug (fun m -> m "BCP: Unknown");
        let decision =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
          Heuristics.best_unassigned vars s.a s.h
          |> Option.value_exn ~error:(Error.of_string "No unassigned variable")
        in
        Todo.part 2 "Cdcl.solve: branching and backtracking"

  let rec run () : Solution.t =
    let s = State.init in
    try
      let s' = solve s in
      SATISFIABLE s'.a.nu
    with
    | Backtrack _ ->
        (* backtracked to the initial level, so unsat overall *)
        Logs.debug (fun m -> m "Backtracked to the initial level");
        (* produce a proof script consisting of all learned lemmas,
           followed by the proof of the empty clause *)
        UNSATISFIABLE (Script.make (List.rev !lemmas) (Proof.fact Clause.empty))
    | Restart ->
        (* restart the solver *)
        run ()

  (** Solving result *)
  let result = run ()
end

(** Run CDCL algorithm *)
let run (desc : Description.t) : Solution.t =
  (* create a solver module and run the solver *)
  let module Solver = Make (struct
    let desc = desc
  end) in
  Solver.result
