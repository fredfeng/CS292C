Inductive day : Type :=
  | mon
  | tue
  | wed
  | thurs
  | fri
  | sat
  | sun.


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
  
Compute (next mon).
Compute (next (next mon)).
Check mon.

Theorem my_first_theorem: next sun = mon.
Proof.
  simpl. (* tactic *)
  reflexivity.
Qed.


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


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "- x" := (negb x).

Compute (true || false).


Theorem andb_false_l: forall (b: bool), andb false b = false.
Proof.
  (* universal instantiation *)
  intro.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r: forall b, andb b false = false.
Proof.
  intro.
  (* case analysis *)
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem negb_is_involutive: 
  forall b, - (- b) = b.
Proof.
Admitted.

End MyBool.


Module MyNat.

Inductive nat : Type := 
  | O
  | S (n: nat).
  
(*. 3 *)
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

Definition mult (m: nat) (n: nat) : nat.
Admitted.

Definition three := (S (S (S O))).


End MyNat.

Compute 3 + 4.

Theorem trivial: forall n m, n = m -> n + n = m + m.
Proof.
 intros.
 (* proof by substitution/rewrite *)
 rewrite <- H.
 reflexivity.
Qed.
