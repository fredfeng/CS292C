(** Potentially unknown boolean *)
Inductive ubool : Type :=
  | T (* true *)
  | U (* unknown *)
  | F (* false *)
  .

(** Negation *)
Definition negu (u: ubool) : ubool :=
  match u with
  | T => F
  | U => U
  | F => T
  end.
  
(** Conjunction *)
Definition andu (u1: ubool) (u2: ubool) : ubool.
Admitted.
  
(** Disjunction *)
Definition oru (u1: ubool) (u2: ubool) : ubool.
Admitted.
  
Notation "x && y" := (andu x y).
Notation "x || y" := (oru x y).
Notation "- x" := (negu x).

Theorem negu_negu: forall u, - - u = u.
Proof.
Admitted.


Theorem andu_self: forall u, u && u = u.
Proof.
Admitted.

Theorem de_morgan_andu: forall u1 u2, - (u1 && u2) = - u1 || - u2.
Proof.
Admitted.

Theorem andu_comm: forall u1 u2, u1 && u2 = u2 && u1.
Proof.
Admitted.

Theorem andu_assoc: forall u1 u2 u3, u1 && (u2 && u3) = u1 && u2 && u3.
Proof.
Admitted.


Theorem andu_distr_oru: forall u1 u2 u3, u1 && (u2 || u3) = u1 && u2 || u1 && u3.
Proof.
Admitted.


(** For the following theorems, do NOT use destruct to perform case analysis. *)
Module NoDestruct.(** Potentially unknown boolean *)
Inductive ubool : Type :=
  | T (* true *)
  | U (* unknown *)
  | F (* false *)
  .

(** Negation *)
Definition negu (u: ubool) : ubool :=
  match u with
  | T => F
  | U => U
  | F => T
  end.
  
(** Conjunction *)
Definition andu (u1: ubool) (u2: ubool) : ubool.
Admitted.
  
(** Disjunction *)
Definition oru (u1: ubool) (u2: ubool) : ubool.
Admitted.
  
Notation "x && y" := (andu x y).
Notation "x || y" := (oru x y).
Notation "- x" := (negu x).

Theorem negu_negu: forall u, - - u = u.
Proof.
Admitted.


Theorem andu_self: forall u, u && u = u.
Proof.
Admitted.

Theorem de_morgan_andu: forall u1 u2, - (u1 && u2) = - u1 || - u2.
Proof.
Admitted.

Theorem andu_comm: forall u1 u2, u1 && u2 = u2 && u1.
Proof.
Admitted.

Theorem andu_assoc: forall u1 u2 u3, u1 && (u2 && u3) = u1 && u2 && u3.
Proof.
Admitted.


Theorem andu_distr_oru: forall u1 u2 u3, u1 && (u2 || u3) = u1 && u2 || u1 && u3.
Proof.
Admitted.


(** For the following theorems, you may NOT use destruct to perform case analysis. 
    Instead, use [rewrite] and previously proven theorems. *)
Module NoDestruct.

Theorem de_morgan_oru: forall u1 u2, - (u1 || u2) = -u1 && -u2.
Proof.
  intros.
  rewrite <- negu_negu with (u := -u1 && -u2).
Admitted.

Theorem oru_self: forall u, u || u = u.
Proof.
  intros.
  rewrite <- negu_negu with (u := u || u).
Admitted.

Theorem oru_comm: forall u1 u2, u1 || u2 = u2 || u1.
Proof.
Admitted.

Theorem oru_assoc: forall u1 u2 u3, u1 || (u2 || u3) = u1 || u2 || u3.
Proof.
Admitted.

Theorem oru_distr_andu: forall u1 u2 u3, u1 || (u2 && u3) = (u1 || u2) && (u1 || u3).
Proof.
Admitted.

End NoDestruct.



Theorem de_morgan_oru: forall u1 u2, - (u1 || u2) = -u1 && -u2.
Proof.
  intros.
  rewrite <- negu_negu.
Admitted.

Theorem oru_comm: forall u1 u2, u1 || u2 = u2 || u1.
Proof.
Admitted.

Theorem oru_assoc: forall u1 u2 u3, u1 || (u2 || u3) = u1 || u2 || u3.
Proof.
Admitted.

Theorem oru_self: forall u, u || u = u.
Proof.
  intros.
  rewrite <- negu_negu with (u := u || u).
Admitted.

Theorem oru_distr_andu: forall u1 u2 u3, u1 || (u2 && u3) = (u1 || u2) && (u1 || u3).
Proof.
  intros.
  rewrite <- negu_negu with (u := u1 || u2).
Admitted.

End NoDestruct.
