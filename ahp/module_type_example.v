Require Import Lia.
Require Import NArith. Open Scope N_scope.

(* Type class definition *)
Module Type Bound.
  (* Type *)
  Parameter t : Type.

  (* Constants *)
  Parameter MIN : t.
  Parameter MAX : t.

  (* Computational functions *)
  Parameter pred : t -> t.
  Parameter succ : t -> t.

  (* Comparison operators *)
  Parameter eq : t -> t -> Prop.
  Parameter le : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  (* Prove decidability of operators *)
  Axiom eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Axiom le_dec : forall x y, {le x y} + {~ le x y}.
  Axiom lt_dec : forall x y, {lt x y} + {~ lt x y}.

  (* Properties of eq for use in proofs *)
  Axiom eq_refl : forall x, eq x x.

  (* Properties of le for use in proofs *)
  Axiom le_refl : forall x, le x x.
  Axiom le_antisymm : forall x y, le x y -> le y x -> x = y.
  Axiom le_trans : forall x y z, le x y -> le y z -> le x z.

  (* Properties of lt for use in proofs *)
  Axiom lt_irrefl : forall x, ~ lt x x.
  Axiom lt_asymm : forall x y, lt x y -> ~ lt y x.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

  (* Properties of bounds, relating constants, operators, and functions *)
  Axiom le_succ_r : forall x y, le x y -> le x (succ y).
  Axiom le_pred_l : forall x y, le x y -> le (pred x) y.
  Axiom le_pred_lt : forall x y, lt MIN x -> le x (pred y) -> lt x y.
  Axiom lt_succ_le : forall x y, lt x MAX -> le (succ x) y -> lt x y.
End Bound.

(* Type class instance *)
Module Byte <: Bound.

Record byte := mkbyte {
  val : N;
  range : val < 256;
}.

Definition t := byte.

Definition MIN : byte := mkbyte 0 eq_refl.
Definition MAX : byte := mkbyte 255 eq_refl.

Definition eq (x y : byte) : Prop := N.eq x.(val) y.(val).
Definition le (x y : byte) : Prop := N.le x.(val) y.(val).
Definition lt (x y : byte) : Prop := N.lt x.(val) y.(val).

Theorem eq_dec : forall x y, {eq x y} + {~ eq x y}.
Proof.
  unfold eq. destruct x, y. intros. cbn.
  destruct (N.eqb val0 val1) eqn:?.
  - left. now apply N.eqb_eq.
  - right. now apply N.eqb_neq.
Qed.

Theorem le_dec : forall x y, {le x y} + {~ le x y}.
Proof.
  unfold le. destruct x, y. intros. cbn.
  destruct (N.leb val0 val1) eqn:?.
  - left. now apply N.leb_le.
  - right. now apply N.leb_nle.
Qed.

Theorem lt_dec : forall x y, {lt x y} + {~ lt x y}.
Proof.
  unfold lt. destruct x, y. intros. cbn.
  destruct (N.ltb val0 val1) eqn:?.
  - left. now apply N.ltb_lt.
  - right. now apply N.ltb_nlt.
Qed.

Lemma N_succ_range : forall x, ~ eq x MAX -> N.succ x.(val) < 256.
Proof. unfold eq, N.eq. destruct x. cbn. lia. Qed.

Definition succ (x : byte) : byte :=
  match eq_dec x MAX with
  | left _ => x
  | right pf => mkbyte (N.succ x.(val)) (N_succ_range _ pf)
  end.

Definition pred (x : byte) : byte :=
  match eq_dec x MIN with
  | left _ => mkbyte (N.pred x.(val)) (N.lt_lt_pred _ _ x.(range))
  | right _ => x
  end.

Theorem eq_refl : forall x, eq x x. Admitted.

Theorem le_refl : forall x, le x x. Admitted.
Theorem le_antisymm : forall x y, le x y -> le y x -> x = y. Admitted.
Theorem le_trans : forall x y z, le x y -> le y z -> le x z. Admitted.

Theorem lt_irrefl : forall x, ~ lt x x. Admitted.
Theorem lt_asymm : forall x y, lt x y -> ~ lt y x. Admitted.
Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z. Admitted.

Theorem le_succ_r : forall x y, le x y -> le x (succ y). Admitted.
Theorem le_pred_l : forall x y, le x y -> le (pred x) y. Admitted.
Theorem le_pred_lt : forall x y, lt MIN x -> le x (pred y) -> lt x y. Admitted.
Theorem lt_succ_le : forall x y, lt x MAX -> le (succ x) y -> lt x y. Admitted.

End Byte.
