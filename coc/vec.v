(** * Vector type with dependent length and arbitrary-length constructor *)

Inductive vec (A : Type) : nat -> Type :=
  | VecNil : vec A 0
  | VecCons (x : A) (n : nat) : vec A n -> vec A (S n).

Arguments VecNil {_}.
Arguments VecCons {_} _ _.

Check VecCons true _ (VecCons false _ (VecCons false _ VecNil)).

Fixpoint append {A n m} (v : vec A n) (w : vec A m) : vec A (n + m) :=
  match v with
  | VecNil => w
  | VecCons x _ v' => VecCons x _ (append v' w)
  end.

Fixpoint mkvec_type_ (A : Type) (n m : nat) : Type :=
  match n with
  | 0 => vec A m
  | S n => A -> mkvec_type_ A n (S m)
  end.
Definition mkvec_type (A : Type) (n : nat) : Type := mkvec_type_ A n 0.

Compute mkvec_type nat 0.
Compute mkvec_type nat 5.

Fixpoint mkvec_ (A : Type) (n m : nat) (v : vec A m) : mkvec_type_ A n m :=
  match n with
  | 0 => v
  | S n => fun a : A => mkvec_ A n (S m) (VecCons a _ v)
  end.
Definition mkvec (A : Type) (n : nat) : mkvec_type A n := mkvec_ A n 0 VecNil.

Compute mkvec nat 0.
Compute mkvec nat 5.
Compute mkvec nat 5 1 2 3 4 5.
