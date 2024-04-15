open Base

(** Substitutions *)
module Subst = struct
  open Lang

  (** [aexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec aexp (x : string) (e : aexp) (c : aexp) : aexp =
    match c with _ -> Todo.at_level 1 ~msg:"Verify.Subst.aexp"

  (** [bexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec bexp (x : string) (e : aexp) (c : bexp) : bexp =
    match c with _ -> Todo.at_level 1 ~msg:"Verify.Subst.bexp"

  (** [formula x e f] substitutes all occurrences of [x] in [f] with [e] *)
  let rec formula (x : string) (e : aexp) (f : formula) : formula =
    match f with _ -> Todo.at_level 1 ~msg:"Verify.Subst.formula"
end

(** Lift a [bexp] into a [formula] *)
let rec bexp_to_formula (b : Lang.bexp) : Lang.formula =
  Todo.at_level 1 ~msg:"Verify.bexp_to_formula"

(** Make a verifier for a method in a difny program *)
module Make (S : sig
  val prog : Lang.prog
  (** ambient program *)

  val meth : Lang.meth
  (** method to verify *)
end) =
struct
  open Lang

  (** [INTERNAL] Mutable reference (i.e. pointer) to the current gamma *)
  let gamma_ref = ref (S.meth.locals @ S.meth.params)

  (** [INTERNAL] Retrieve the current gamma *)
  let gamma () = !gamma_ref

  (** Update gamma to map a new variable with its type *)
  let add_gamma (x : string) (t : ty) : unit = gamma_ref := (x, t) :: !gamma_ref

  (** [INTERNAL] Counter to generate fresh variables *)
  let counter = ref 0

  (** Generate a fresh variable using the hint, and record its type in gamma *)
  let fresh_var (t : ty) ~(hint : string) =
    let i = !counter in
    counter := !counter + 1;
    let x = Fmt.str "$%s_%d" hint i in
    add_gamma x t;
    x

  (** Compute the list of modified variables in a statement *)
  let rec modified (s : stmt) : string list =
    match s with _ -> Todo.at_level 1 ~msg:"Verify.modified"

  (** Compute the list of unique modified variables in a sequence of statements *)
  and modified_block (stmts : block) : string list =
    (* for each stmt, compute the list of modified variabls ("map"),
       and then concatenate all lists together ("concat") *)
    let xs = List.concat_map ~f:modified stmts in
    (* deduplicate and sort the list *)
    List.dedup_and_sort ~compare:String.compare xs

  (** Compile a statement into a sequence of guarded commands *)
  let rec compile (c : stmt) : gcom list =
    match c with
    | Assign { lhs; rhs } -> Todo.at_level 1 ~msg:"Verify.compile: Assign"
    | If { cond; els; thn } -> Todo.at_level 1 ~msg:"Verify.compile: If"
    | While { cond; inv; body } -> Todo.at_level 1 ~msg:"Verify.compile: While"
    | Call { lhs; callee; args } -> Todo.at_level 3 ~msg:"Verify.compile: Call"
    | Havoc x -> [ Havoc x ]
    | Assume f -> [ Assume f ]
    | Assert f -> [ Assert f ]
    | Print _ -> []

  (** For each statement in a block, compile it into a list of guarded 
      commands ("map"), and then concatenate the result ("concat") *)
  and compile_block : block -> gcom list = List.concat_map ~f:compile

  (** Compute weakest-pre given a guarded command and a post formula *)
  let rec wp (g : gcom) (f : formula) : formula =
    match g with
    | Assume f' -> Todo.at_level 1 ~msg:"Verify.wp: Assume"
    | Assert f' -> Todo.at_level 1 ~msg:"Verify.wp: Assert"
    | Havoc x -> Todo.at_level 1 ~msg:"Verify.wp: Havoc"
    | Seq cs -> Todo.at_level 1 ~msg:"Verify.wp: Seq"
    | Choose (c1, c2) -> Todo.at_level 1 ~msg:"Verify.wp: Choose"

  (** Propagate the post-condition backwards through a sequence of guarded
      commands using [wp] *)
  and wp_seq (gs : gcom list) (phi : formula) : formula =
    List.fold_right ~init:phi ~f:wp gs

  (** Verify the method passed in to this module *)
  let result : unit =
    (* print method id and content *)
    Logs.debug (fun m -> m "Verifying method %s:" S.meth.id);
    Logs.debug (fun m -> m "%a" Pretty.meth S.meth);

    (* compile method to guarded commands *)
    let gs =
      compile_block (Todo.at_level 2 ~msg:"compile_block" ~dummy:S.meth.body)
    in
    Logs.debug (fun m -> m "Guarded commands:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) gs);

    (* compute verification condition (VC) using weakest-precondition *)
    let vc = wp_seq gs (FBool true) in
    Logs.debug (fun m -> m "Verification condition:");
    Logs.debug (fun m -> m "%a" Pretty.formula vc);

    (* check if the VC is valid under the current gamma *)
    let status = Smt.check_validity (gamma ()) vc in
    match status with
    | Smt.Valid -> Logs.app (fun m -> m "%s: verified" S.meth.id)
    | Smt.Invalid cex ->
        Logs.app (fun m -> m "%s: not verified" S.meth.id);
        Logs.app (fun m -> m "Counterexample:");
        Logs.app (fun m -> m "%s" cex)
    | Smt.Unknown -> Logs.app (fun m -> m "%s: unknown" S.meth.id)
  (* this function doesn't return anything, so it implicitly
     returns the unit value "()" *)
end

(** Public function for verifying a difny method *)
let go (prog : Lang.prog) (meth : Lang.meth) : unit =
  (* construct a verifier module (verification happens during module construction) *)
  let module Verifier = Make (struct
    let prog = prog
    let meth = meth
  end) in
  (* retrieve the result, which is just a unit value *)
  Verifier.result
