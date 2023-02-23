Require Import Arith.
Import IfNotations.

Inductive term :=
  | TVar (index : nat)
  | TArrow (lhs rhs : term)
  | TNum
  | TBool.

Fixpoint term_eq (τ0 τ1 : term) : bool :=
  match τ0, τ1 with
  | TVar n0, TVar n1 => n0 =? n1
  | TArrow l0 r0, TArrow l1 r1 => term_eq l0 l1 && term_eq r0 r1
  | TNum, TNum | TBool, TBool => true
  | _, _ => false
  end.

Fixpoint occurs (τ : term) (n : nat) : bool :=
  match τ with
  | TVar n0 => n0 =? n
  | TArrow l r => occurs l n || occurs r n
  | TNum | TBool => false
  end.

Definition substitution : Type := nat -> option term.

Definition empty : substitution := fun _ => None.

Definition insert (σ : substitution) (n : nat) (t : term) : option substitution :=
  if occurs t n then None
  else Some (fun n1 => if n1 =? n then Some t else σ n).

Fixpoint unify (τ0 τ1 : term) (σ : substitution) : option substitution :=
  match τ0, τ1 with
  | TVar n0, _ => insert σ n0 τ1
  | _, TVar n1 => insert σ n1 τ0
  | TArrow l0 r0, TArrow l1 r1 =>
      let σ0 := unify l0 l1 σ in if σ0 is Some σ0 then
      let σ1 := unify r0 r1 σ0 in if σ1 is Some σ1 then
      Some σ1
      else None else None
  | TNum, TNum => Some σ
  | TBool, TBool => Some σ
  | _, _ => None
  end.

Compute unify (TVar 0) (TVar 0) empty.
Compute unify (TVar 0) (TVar 1) empty.
Compute unify (TVar 0) (TArrow (TVar 0) (TVar 2)) empty.
