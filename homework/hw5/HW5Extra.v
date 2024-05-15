Require Import FunctionalExtensionality.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.

(*****************************************************
 *           Theorems about partial maps             *
 *****************************************************)
Section Map.

(* Assume the value type V is any type. Once this [Section] ends,
  all functions and theorems that mention V will be generalized into
  [forall V, ...] *)
Variable V : Type.

Definition total_map (A: Type) := nat -> A.

Definition read {A: Type} (m: total_map A) (k: nat) := m k.

Definition write {A: Type} (m: total_map A) (k: nat) (x: A) : total_map A :=
  fun k' => if k =? k' then x else read m k'.

Definition partial_map (A: Type) := total_map (option A).

Definition map := partial_map V.

Definition empty : map := fun x => None.

Theorem read_empty: forall k,
  read empty k = None.
Proof.
Admitted.

(* Nat.eqb is a sound and complete decision procedure for nat equalities *)
Lemma eqb_true: forall k1 k2,
  k1 =? k2 = true <-> k1 = k2.
Proof. 
  (* you do not need to understand this proof *)
  intros. destruct (Nat.eqb_spec k1 k2); split; congruence.
Qed.

Lemma eqb_false: forall k1 k2,  
  k1 =? k2 = false <-> k1 <> k2.
Proof.
  intros.
  pose proof (eqb_true k1 k2) as H.
  split.
  - admit.
  - admit.
Admitted.

Theorem write_eq: forall (m: map) k v,
  read (write m k v) k = v.
Proof.
  intros. unfold read, write.
  destruct (k =? k) eqn:E. 
  - reflexivity.
  - (* change goal into False *)
    exfalso.
    admit.
Admitted.

Theorem write_neq: forall (m: map) k1 k2 v,
  k2 <> k1 ->
  read (write m k2 v) k1 = read m k1.
Proof.
  intros. unfold write, read.
  destruct (k2 =? k1) eqn:E.
  - exfalso. admit.
  - reflexivity.
Admitted.

(* Two maps are equal if they agree on every possible read *)
Lemma map_extensionality: forall (m1 m2: map),
  (forall k, read m1 k = read m2 k) ->
  m1 = m2.
Proof.
  intros.
  extensionality k'.
Admitted.


(* [restrict m p] preserves all keys that satisfy [p] and erases all keys
  that do not satisfy [p] (i.e., replace them with [None]) *)
Definition restrict (m: map) (p: nat -> bool) : map :=
  fun k => 
    if p k then read m k
    else None.

Theorem restrict_empty: forall p,
  restrict empty p = empty.
Proof.
Admitted.

Theorem restrict_read: forall m p k,
  read (restrict m p) k = 
    if p k then read m k else None.
Proof.
Admitted.

Theorem write_restrict: forall m p k v,
  restrict (write m k v) p = 
    write (restrict m p) k (if p k then v else None).
Proof.
  intros.
  apply map_extensionality. intro k'.
  pose proof (eqb_true k k') as H.
  unfold restrict, write, read.
  (* [T1; T2] means "apply T1 to the current goal, and for every generated sub-goal, apply T2" *)
  destruct (p k) eqn:Hpk; 
  destruct (p k') eqn:Hpk'; 
  destruct (k =? k') eqn:E;
  (* filter out the trivial sub-goals like [v = v] *)
  trivial.
  - exfalso. admit.
  - exfalso. admit.
Admitted.

Theorem restrict_write_true: forall m p k v,
  p k = true ->
  write (restrict m p) k v = restrict (write m k v) p.
Proof.
  intros.
  apply map_extensionality. intro k'.
  admit.
Admitted.

Theorem restrict_equiv: forall m p q,
  (forall k, p k = q k) ->
  restrict m p = restrict m q.
Proof.
  intros.
  apply map_extensionality. intro k.
Admitted.

End Map.



(*****************************************************
 *                        SAT                        *
 *****************************************************)

(* Potentially unknown booleans:
  T -> Some true
  U -> None
  F -> Some false *)
Definition ubool : Type := option bool.

(* Although the law of excluded middle [P \/ ~P] is not provable 
  in Coq in general, it is provable in simple cases like when [P] is [u = None] *)
Theorem ubool_none_decidable: forall (u: ubool),
  u = None \/ u <> None.
Proof.
Admitted.

Definition option_map {A B: Type} (o: option A) (f: A -> B) :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Definition negu (u: ubool) : ubool := option_map u negb.

Definition andu (u1: ubool) (u2: ubool) : ubool.
Admitted.

Definition oru (u1: ubool) (u2: ubool) : ubool.
Admitted.

Theorem andu_true: forall u1 u2,
  andu u1 u2 = Some true <->
  (u1 = Some true /\ u2 = Some true).
Proof.
Admitted.

Theorem andu_false: forall u1 u2,
  andu u1 u2 = Some false <->
  (u1 = Some false \/ u2 = Some false).
Proof.
Admitted.

(* Enumerate the cases in which [andu u1 u2] returns None.
  The returned [Prop] must be a proposition involving
  [u1 = ...] or [u2 = ...], connected using \/, /\, ->, or ~.
  You may NOT use [andu_none_cases u1 u2 := andu u1 u2 = None],
  which defeats the point of this exercise. *)
Definition andu_none_cases (u1 u2: ubool) : Prop.
Admitted.

Theorem andu_none: forall u1 u2,
  andu u1 u2 = None <->
  andu_none_cases u1 u2.
Proof.
Admitted.

Inductive formula :=
  | var (x: nat)
  | neg (f: formula)
  | and (f1: formula) (f2: formula)
  | or (f1: formula) (f2: formula).

(* An assignment [nu] is a partial map from variables to [bool],
  i.e. total map to [ubool]. *)
Definition nu: Type := partial_map bool.

(* Evaluate a formula under a variable map *)
Fixpoint eval (v: nu) (f: formula) : ubool :=
  match f with
  | var x => read v x
  | neg f' => negu (eval v f')
  | and f1 f2 => andu (eval v f1) (eval v f2)
  | or f1 f2 => oru (eval v f1) (eval v f2)
  end.

(* Some useful notations: *)
Notation "v |= f" := (eval v f = Some true) (at level 60). (* v satisfies f *)
Notation "v |!= f" := (eval v f = Some false) (at level 60). (* v does not satisfy f *)
Notation "v |?= f" := (eval v f = None) (at level 60). (* v may or may not satisfy f *)

Arguments empty {V}.
Arguments restrict {V}.

(* Evaluating any formula under the empty map gives "unknown" *)
Theorem eval_empty: forall f,
  empty |?= f.
Proof.
  induction f.
Admitted.

(* If f evaluates to "unknown" under a map [v],
  then evaluating f under any restricted [v] also gives "unknown" *)
Theorem eval_none: forall f v p,
  eval v f = None ->
  eval (restrict v p) f = None.
Proof.
  induction f; simpl; intros.
  - admit.
  - admit.
  - rewrite andu_none. admit.
  - admit.
Admitted.