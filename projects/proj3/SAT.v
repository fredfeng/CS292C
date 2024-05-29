Require Import List.
Require Import Arith.
Require Import ssreflect ssrbool.
Require Import Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Proj3.CpdtTactics.

Set Asymmetric Patterns.

Definition var := nat.

Section Map.

Variable A: Type.

Definition total_map (X: Type) := var -> X.

Definition map := total_map (option A).

Definition empty : map := fun _ => None.

Definition write {X: Type} (v: total_map X) (x: var) (r: X) : total_map X :=
  fun (y: var) => if x =? y then r else v y.

Definition restrict (p: var -> bool) (v: map) : map :=  
  fun (x: var) => if p x then v x else None.

Definition overwrite {X: Type} (v: total_map X) p r :=
  fun x => if p x then r else v x.

End Map.

Arguments empty {A}.
Arguments write {X}.
Arguments restrict {A}.
Arguments overwrite {X}.


Declare Scope map_scope.
Delimit Scope map_scope with map.

Notation "m '[' x '|->' v ']'" := (write m x v)
  (at level 60, v at next level, right associativity) : map_scope.
Notation "v |_ p" := (restrict p v) (at level 60) : map_scope.
Notation "v |_> n" := (restrict (fun m => n <? m) v) (at level 60) : map_scope.
Notation "v |_>= n" := (restrict (fun m => n <=? m) v) (at level 60) : map_scope.
Notation "v |_< n" := (restrict (fun m => m <? n) v) (at level 60) : map_scope.
Notation "v |_<= n" := (restrict (fun m => m <=? n) v) (at level 60) : map_scope.
Notation "m '[' p '?' v ']'" :=  (overwrite m p v)
  (at level 60, v at next level, right associativity) : map_scope.

Open Scope map_scope.


(*****************************************************
 *                      Solver                       *
 *****************************************************)

Inductive formula: Type :=
  | Var (x: var)
  | Neg (f: formula)
  | And (f1: formula) (f2: formula)
  | Or (f1: formula) (f2: formula).

Definition nu := map bool.

Definition option_merge {A: Type} (x: option A) (y: option A) :=
  match x with
  | Some _ => x
  | None => y
  end.

Notation "x <|> y" := (option_merge x y) (right associativity, at level 60).

Definition negu : option bool -> option bool.
Admitted.

Definition andu : option bool -> option bool -> option bool.
Admitted.

Definition oru : option bool -> option bool -> option bool.
Admitted.

Fixpoint eval (v: nu) (f: formula) : option bool := 
  match f with
  | Var x => v x
  | Neg f => negu (eval v f)
  | And f1 f2 => andu (eval v f1) (eval v f2)
  | Or f1 f2 => oru (eval v f1) (eval v f2)
  end.

Notation "f1 ||| f2" := (oru f1 f2) (at level 40).
Notation "f1 &&& f2" := (andu f1 f2) (at level 40).


(* v satisfies f *)
Notation "v '|=' f" := (eval v f = Some true) (at level 100).

(* v does not satisfy f *)
Notation "v '|!=' f" := (eval v f = Some false) (at level 100).

(* v may or may not satisfy f *)
Notation "v '|?=' f" := (eval v f = None) (at level 100).

Fixpoint solve (n: var) (v: nu) (f: formula) : option nu :=
  match eval v f with
  | Some true => Some v
  | Some false => None
  | None =>
    match n with
    | 0 => None
    | S n' => 
          solve n' (v [n' |-> Some true]) f
          <|> solve n' (v [n' |-> Some false]) f
      end
  end.

Fixpoint max_var (f: formula) : nat :=
  match f with
  | Var n => n
  | Neg f => max_var f
  | And f1 f2 => Nat.max (max_var f1) (max_var f2)
  | Or f1 f2 => Nat.max (max_var f1) (max_var f2)
  end.

Definition z4 (f: formula) :=
  let m := max_var f in
  solve (S m) empty f.

(* Helper functions to convert nu into a list
*)

Fixpoint nu_to_list_n (n: var) (v: nu) : list (var * bool) :=
  match n with
  | 0 => nil
  | S n' => 
    match v n with
    | None => nu_to_list_n n' v
    | Some b => (n, b) :: nu_to_list_n n' v
    end
  end.

Definition run f :=
  let m := max_var f in
  option_map (nu_to_list_n m) (z4 f).

Example test_solve_1 :
  run (Or (Var 1) (Neg (Var 1))) = Some ((1, true)::nil).
(* After you copied over your negu, andu, and oru, uncomment below *)
(* Proof. reflexivity. Qed. *)
Example test_solve_2 : 
  run (And (Var 1) (Neg (Var 1))) = None.
(* After you copied over your negu, andu, and oru, uncomment below *)
(* Proof. reflexivity. Qed. *)



(*****************************************************
 *           Theorems about partial maps             *
 *****************************************************)
Lemma write_read_eq: forall (A: Type) x r (v: map A),
  (v [ x |-> r]) x = r.
Proof.
Admitted.

Lemma write_read_neq: forall (A: Type) x y r (v: map A),
  x <> y ->
  (v[x |-> r]) y = v y.
Proof.
Admitted.

Lemma write_read: forall (A: Type) (v: map A) x y r,
  (v [x |-> r]) y = if x =? y then r else v y.
Proof.
Admitted.

(* Add your own lemmas here *)



(*****************************************************
 *             Theorems about denotation             *
 *****************************************************)

Ltac case_u :=
  match goal with
  | H: ?T |- _ =>
    match T with
    | bool =>
      let E := fresh "E" in
      destruct H
    | option bool => 
      let E := fresh H in
      destruct H
    | _ => fail 1
    end
  | _ => fail 1
  end.

Ltac cases := repeat case_u.

(* Reflect operator behaviors into exhaustive case analysis *)

Lemma negu_some: forall u b,
  negu u = Some b <->
  u = Some (negb b).
(* After you copied over your negu, andu, and oru, uncomment below *)
(* Proof. intros. cases; crush. Qed. *)

Lemma andu_none: forall u1 u2,
  u1 &&& u2 = None <->
  (u1 = None /\ u2 = Some true) \/
  (u2 = None /\ u1 = Some true) \/
  (u1 = None /\ u2 = None).
(* After you copied over your negu, andu, and oru, uncomment below *)
(* Proof. intros. cases; crush. Qed. *)

Lemma andu_some: forall u1 u2 b,
  u1 &&& u2 = Some b <->
  ( (b = true -> (u1 = Some true /\ u2 = Some true))
  /\ (b = false -> (u1 = Some false \/ u2 = Some false))).
(* After you copied over your negu, andu, and oru, uncomment below *)
(* Proof. intros. cases; crush. Qed. *)

(* Add your own lemmas here *)



(*****************************************************
 *               Theorems about eval                 *
 *****************************************************)

Lemma eval_extend: forall v f p b,
  eval (v |_ p) f = Some b ->
  eval v f = Some b.
Proof.
Admitted.

(* Add your own lemmas here *)



(*****************************************************
 *            Soundness and Completeness             *
 *****************************************************)

Lemma solve_sound: forall n v f u,
  solve n v f = Some u ->
  u |= f.
Proof.
  induction n.
Admitted.

Lemma solve_complete: forall n v f u,
  (* v [0..n-1] is unassigned *)
  (forall x, x < n -> v x = None) ->
  (* v [n..] is assigned *)
  (forall x, x >= n -> v x <> None) ->
  solve n v f = None ->
  (* u agrees with v on >= n *)
  u |_>= n = v |_>= n ->
  (* u cannot satisfy f *)
  ~(u |= f).
Proof.
  induction n.
Admitted.


(*****************************************************
 *                       z4 solver                   *
 *****************************************************)

Theorem z4_sound: forall f v,
  z4 f = Some v ->
  v |= f.
Proof.
  unfold z4. intros.
  eapply solve_sound.
  apply H.
Qed.

Theorem z4_complete: forall f,
  z4 f = None ->
  forall v, ~(v |= f).
Proof.
Admitted.



(*****************************************************
 *                     Finale                        *
 *****************************************************)

(* SAT is decidable *)

Definition decidable (P: Prop) := P \/ ~P.

Definition is_sat (f: formula) : Prop := 
  exists v, eval v f = Some true.

Theorem sat_dec: forall f,
  decidable (is_sat f).
Proof.
Admitted.

(* Whether f is sat is reflected by whether z4 returns [Some ..] *)

Definition is_some {A} (o: option A) : bool :=
  if o then true else false.

(* You first saw [reflect] in IndProp. It's actually part of ssreflect library *)
Print Bool.reflect.

Theorem z4_spec: forall f,
  reflect (is_sat f) (is_some (z4 f)).
Proof.
Admitted.