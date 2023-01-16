Require Import List. Import ListNotations.

Module ND.

Inductive ND (A : Type) : Type :=
  | SuccessND (a : A)
  | FailND
  | OrND (l r : ND A).
Arguments SuccessND {A} _.
Arguments FailND {A}.
Arguments OrND {A} _ _.

Reserved Notation "m '>>=' f" (right associativity, at level 60).

Definition ret {A : Type} (a : A) : ND A :=
  SuccessND a.

Fixpoint bind {A B : Type} (m : ND A) (f : A -> ND B) : ND B :=
  match m with
  | SuccessND a => f a
  | FailND => FailND
  | OrND l r => OrND (l >>= f) (r >>= f)
  end
  where "m '>>=' f" := (bind m f).

(* TODO: Should be a set *)
Fixpoint nd {A : Type} (n : ND A) : list A :=
  match n with
  | SuccessND a => [a]
  | FailND => []
  | OrND l r => nd l ++ nd r
  end.

End ND.
