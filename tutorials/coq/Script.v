(*********************************
 *            May 1              *
 *********************************)

(* [Inductive] defines an "enum" type, just like [type day = ...] in OCaml *)
Inductive day : Type :=
  | mon
  | tue
  | wed
  | thurs
  | fri
  | sat
  | sun.

(* functions are defined using [Definition .. := .. .] *)
Definition next (d: day) : day :=
  match d with
  | mon => tue
  | tue => wed
  | wed => thurs
  | thurs => fri
  | fri => sat
  | sat => sun
  | sun => mon
  end.
  
(* evaluate expressions involving function calls *)
Compute (next mon).
Compute (next (next mon)).

(* ask the type checker for the type of an expression *)
Check mon.

(* we couldn't do this in OCaml! *)
Theorem my_first_theorem: next sun = mon.
Proof.
  simpl. (* tactic *)
  reflexivity. (* everything is equal to themselves *)
Qed.


(* a [Module] restricts definitions within a scope *)
Module MyBool.

Inductive bool : Type :=
  | true
  | false.
  
Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
  
Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true => true
    | false => false
    end
  | false => false
  end.
  
Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => 
    match b2 with
    | true => true
    | false => false
    end
  end.

(* we can change the parser at runtime! :Exploding-Head-Emoji *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "- x" := (negb x).

Compute (true || false).

(* we can prove forall-propositions! SMT solvers suck at these *)
Theorem andb_false_l: forall (b: bool), andb false b = false.
Proof.
  (* universal instantiation *)
  intro.
  simpl.
  reflexivity.
Qed.

(* should be similar, right?*)
Theorem andb_false_r: forall b, andb b false = false.
Proof.
  intro.
  simpl. 
  (* NOTHING HAPPENS! 
    because [andb] pattern-matches on the first argument, which in this case 
    is an arbitrary boolean [b]. So we can't simplify any further *)
Abort.

(* second try *)
Theorem andb_false_r: forall b, andb b false = false.
Proof.
  intro.
  (* case analysis *)
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


End MyBool.


Module MyNat.

Inductive nat : Type := 
  | O
  | S (n: nat).
  
(* this represents 3 *)
Check (S (S (S O))).
  
Definition pred (n: nat) : nat := 
  match n with 
  | O => O
  | S n' => n'
  end.

Fixpoint plus (m: nat) (n: nat) : nat :=
  match m with 
  | O => n
  | S m' => S (plus m' n)
  end.

End MyNat.

(* luckily Coq has built-in definitions and parsers for [nat] *)
Compute 3 + 4.

Theorem trivial: forall n m, n = m -> n + n = m + m.
Proof.
 intros.
 (* proof by substitution/rewrite *)
 (* [rewrite -> H] means substituting the LHS of H with RHS in the current goal *)
 (* [rewrite <- H] means substituting the RHS of H with LHS in the current goal *)
 rewrite -> H.
 (* also works: [rewrite <- H] *)
 reflexivity.
Qed.

(* In summary, here's what we've learned:
- Commands:
  + [Inductive]: defining new types
  + [Definition]: defining values and functions
  + [Theorem]: defining propositions to be proved
  + [Compute]: evaluating expressions
  + [Check]: computing types of expressions
- Tactics:
  + [simplify]: simplifying expressions by evaluating function calls
  + [reflexivity]: proving equality of the form [x = x]
  + [intro] and [intros]: instantiating universally quantified variables
  + [destruct]: case analysis
  + [rewrite]: substituting equalities
 *)

(*********************************
 *            May 6              *
 *********************************)
From LF Require Export Basics.

Theorem add_0_l: forall n, 0 + n = n.
Proof.
  intros.
  (* search for parser definition of "+" *)
  Locate "+". 
  (* ==>
    Notation "{ A } + { B }" := (sumbool A B) : type_scope (default interpretation)
    Notation "A + { B }" := (sumor A B) : type_scope (default interpretation)
    Notation "x + y" := (Nat.add x y) : nat_scope (default interpretation)
    Notation "x + y" := (sum x y) : type_scope
  *)
  (* print function definition *)
  Print Nat.add. 
  (* ==>
    Nat.add = fix add (n m : nat) {struct n} : nat := match n with
    | 0 => m
    | S p => S (add p m)
    end
    : nat -> nat -> nat

    Arguments Nat.add (n m)%nat_scope
  *)
  simpl.
  reflexivity.
Qed.



Theorem add_0_r: forall n, n + 0 = n.
Proof.
  intros.
  simpl.
  (* "as [|n']" remembers the predecessor as n'.
     "eqn:E" remembers the equation [n = S n'].
  *)
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. f_equal.
Abort.

Theorem add_0_r: forall n, n + 0 = n.
Proof.
  intros.
  simpl.
  (* "as [|n']" remembers the predecessor as n'. *)
  induction n as [|n'].
  - reflexivity.
  - simpl.
    (* the law of congruence: x = y -> f(x) = f(y) *)
    f_equal.
    apply IHn'.
Qed.

(* exercise for you *)
Theorem sub_n_n: forall n, n - n = 0.
Proof.
  Print Nat.sub.
Admitted.


(* Important note on differences between booleans and propositions *)

(* equality comparison between nats *)
Fixpoint eqb (m: nat) (n: nat) : bool := 
  match m with
  | O =>
    match n with
    | O => true
    | _ => false
    end
  | S m' =>
    match n with
    | O => false
    | S n' => eqb m' n'
    end
  end.

Check (eqb 3 3). (* type is [bool] *)
Check (3 = 3). (* type is [Prop] *)
(* Prop stands for proposition! which is different from bool *)

(* Prop: statements to be proved *)
(* decision procedures: functions that return booleans *)


(* sound vs complete 

Example 0: COVID
  Actual behavior: do I have COVID?
  Predicted behavior: does my COVID test say positive?

  Soundness means: positive COVID tests are correct: if the test says YES, then I have COVID.
  Completeness means: if I have COVID, then the test is guaranteed to catch it.

  Unsound: positive test, but actually I don't have COVID (false positive/false alarm)
  Incomplete: I have COVID but test fails to catch it (i.e., test says negative)

In the context of decision procedure...
  Soundness means: if something is true, then my decision procedure will say YES
  Completeness means: if my decision procedure says YES, then the thing is true.

Example 1: Your difny verifier is a decision procedure for program correctness
  soundness means: "verified" programs are actually correct
  completeness means: difny will output "verified" for every correct program

  Soundness is usually easy to prove (just do an induction over all AST cases).
  Completeness is usually much harder. 
  For example, a program can be actually correct but difny may say "not verified" due to missing invariants.

Example 2: DPLL and CDCL are sound and complete decision procedures for SAT.

Example 3. We claim that [eqb] is a sound and complete decision procedure for natural number equality.
*)

Print Nat.eqb.

(* In Coq, the convention is to use "=?" to denote
  decision procedures for deciding equalities *)
Locate "=?".
(* ==>
  Notation "x =? y" := (Basics.eqb x y) : nat_scope (default interpretation)
  Notation "x =? y" := (String.eqb x y) : string_scope
*)

Theorem eqb_is_a_sound_decision_procedure: forall m n, 
  (m =? n) = true -> m = n.
Proof.
  Print eqb.
  induction m as [|m'].
  - intros n H.
    (* base case : m = 0 *)
   (* 0 =? n ==> eqb 0 n *)
   simpl in H.
   destruct n as [|n'].
   + (* n = 0 *)
    reflexivity.
    + (* n = S n' ==> 0 =? S n'*)
    discriminate H.
  - intros.
    destruct n as [|n'].
    + simpl in H.
      (* H: false = true
         this is absurd *)
      discriminate H.
    + (* to prove S m' = S n', suffice to show m' = n' *)
      f_equal.
      apply IHm'.
      (* IHm' has served its purpose, so we let it go *)
      clear IHm'. 
      simpl in H.
      apply H.
      (* alternative: this is also fine: *)
      (* 
      f_equal.
      apply IHm'.
      clear IHm'.
      rewrite <- H.
      simpl.
      reflexivity. *)
Qed.

Theorem eqb_is_a_complete_decision_procedure: forall m n,
  m = n -> (m =? n) = true.
Proof. 
  (* stay tuned! *)
Abort.


(* what we've learned:
  - "f_equal" applies the congruence property of functions:
      if x = y, then f(x) = f(y)
      So if you see constructor(X) = constructor(Y),
      applying f_equal changes the goal into X=Y
  - "discriminate": expressions built from different constructors cannot be equal
      So if you have a hypothesis like false = true (which is absurd)
      [discriminate] discharges the current goal no matter what the goal is.
 *)




(*********************************
 *            May 8              *
 *********************************)
From LF Require Export Induction.

(* product type *)
Inductive natprod :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair n1 n2 => n1
  end.

  
(* In OCaml: constructor (arg1, arg2) *)

Definition snd (p : natprod) : nat.
Admitted.

Definition swap (p: natprod) : natprod :=
  match p with
  | pair n1 n2 => pair n2 n1 
  end.

Theorem swap_swap: forall p,
  swap (swap p) = p.
Proof.
  intros.
  (* destruct: case analysis *)
  destruct p.
  simpl.
  reflexivity.
Qed.



(* list type *)
Inductive natlist : Type :=
  | nil
  | cons (n: nat) (l: natlist).


Notation "x :: l" := (cons x l) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Compute [1;2;3].


Fixpoint length (l: natlist) : nat :=
  match l with
  | [] => 0
  | x::l' => 1 + length l'
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.


Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Compute ([1;2] ++ [3;4]).
(* IN OCaml: @ *)


Fixpoint rev (l: natlist) : natlist :=
  match l with
  | [] => []
  | x::l' => rev l' ++ [x]
  end.


(* let's prove things about lists *)


Lemma length_app: forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl.
    (* (n :: l1) ++ l2 ==> n :: (l1 ++ l2) *)
    (* length (n :: ...) = 1 + length .. *)
    f_equal.
    apply IHl1.
Qed.

(* alternatively, use the following lemma:
  length (l1 ++ [x]) = S (length l1)
 *)

(* worked in class *)
Theorem length_rev: forall (l: natlist),
  length (rev l) = length l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- IHl.
    simpl.
    rewrite length_app.
    simpl.
    Check add_comm.
    rewrite add_comm. (* proved in SF's Induction.v - it's just an easy induction proof on nat *)
    simpl.
    reflexivity.
Qed.



(* but our theorems are much more general! 
  unfortunately, natlists can only hold natural numbers *)

(* in OCaml we can do "int list", "bool list", or "'a list" *)
(* in Java/C++, we can do "List<int>", "List<bool>", or "List<T>"*)

(* this is called _polymorphism_, which Coq also supports 
*)


Module MyList.

Inductive list (X: Type) :=
  | nil
  | cons (x: X) (l: list X).

Check (nil nat).

Check (cons nat 1 (cons nat 2 (nil nat))).

(* there is a way to make Coq infer all of the these type annotations. We'll talk about this next week *)


End MyList.