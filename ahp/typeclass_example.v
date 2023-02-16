Require Import Lia.
Require Import NArith. Open Scope N_scope.

Record byte := mkbyte {
  val : N;
  range : val < 256;
}.

Definition byte_MIN : byte := mkbyte 0 eq_refl.
Definition byte_MAX : byte := mkbyte 255 eq_refl.

Definition byte_eq (x y : byte) : Prop := N.eq x.(val) y.(val).
Definition byte_le (x y : byte) : Prop := N.le x.(val) y.(val).
Definition byte_lt (x y : byte) : Prop := N.lt x.(val) y.(val).

Theorem byte_eq_dec : forall x y, {byte_eq x y} + {~ byte_eq x y}.
Proof.
  unfold byte_eq. destruct x, y. intros. cbn.
  destruct (N.eqb val0 val1) eqn:?.
  - left. now apply N.eqb_eq.
  - right. now apply N.eqb_neq.
Qed.

Theorem byte_le_dec : forall x y, {byte_le x y} + {~ byte_le x y}.
Proof.
  unfold byte_le. destruct x, y. intros. cbn.
  destruct (N.leb val0 val1) eqn:?.
  - left. now apply N.leb_le.
  - right. now apply N.leb_nle.
Qed.

Theorem byte_lt_dec : forall x y, {byte_lt x y} + {~ byte_lt x y}.
Proof.
  unfold byte_lt. destruct x, y. intros. cbn.
  destruct (N.ltb val0 val1) eqn:?.
  - left. now apply N.ltb_lt.
  - right. now apply N.ltb_nlt.
Qed.

Lemma N_succ_range : forall x, ~ byte_eq x byte_MAX -> N.succ x.(val) < 256.
Proof. unfold byte_eq, N.eq. destruct x. cbn. lia. Qed.

Definition byte_succ (x : byte) : byte :=
  match byte_eq_dec x byte_MAX with
  | left _ => x
  | right pf => mkbyte (N.succ x.(val)) (N_succ_range _ pf)
  end.

Definition byte_pred (x : byte) : byte :=
  match byte_eq_dec x byte_MIN with
  | left _ => mkbyte (N.pred x.(val)) (N.lt_lt_pred _ _ x.(range))
  | right _ => x
  end.

Theorem byte_eq_refl : forall x, byte_eq x x. Admitted.

Theorem byte_le_refl : forall x, byte_le x x. Admitted.
Theorem byte_le_antisymm : forall x y, byte_le x y -> byte_le y x -> x = y. Admitted.
Theorem byte_le_trans : forall x y z, byte_le x y -> byte_le y z -> byte_le x z. Admitted.

Theorem byte_lt_irrefl : forall x, ~ byte_lt x x. Admitted.
Theorem byte_lt_asymm : forall x y, byte_lt x y -> ~ byte_lt y x. Admitted.
Theorem byte_lt_trans : forall x y z, byte_lt x y -> byte_lt y z -> byte_lt x z. Admitted.

Theorem byte_le_succ_r : forall x y, byte_le x y -> byte_le x (byte_succ y). Admitted.
Theorem byte_le_pred_l : forall x y, byte_le x y -> byte_le (byte_pred x) y. Admitted.
Theorem byte_le_pred_lt : forall x y, byte_lt byte_MIN x -> byte_le x (byte_pred y) -> byte_lt x y. Admitted.
Theorem byte_lt_succ_le : forall x y, byte_lt x byte_MAX -> byte_le (byte_succ x) y -> byte_lt x y. Admitted.

(* Type class definition *)
Class Bound T := {
  (* Constants *)
  MIN : T;
  MAX : T;

  (* Computational functions *)
  pred : T -> T;
  succ : T -> T;

  (* Comparison operators *)
  eq : T -> T -> Prop;
  le : T -> T -> Prop;
  lt : T -> T -> Prop;

  (* Prove decidability of operators *)
  eq_dec : forall x y, {eq x y} + {~ eq x y};
  le_dec : forall x y, {le x y} + {~ le x y};
  lt_dec : forall x y, {lt x y} + {~ lt x y};

  (* Properties of eq for use in proofs *)
  eq_refl : forall x, eq x x;

  (* Properties of le for use in proofs *)
  le_refl : forall x, le x x;
  le_antisymm : forall x y, le x y -> le y x -> x = y;
  le_trans : forall x y z, le x y -> le y z -> le x z;

  (* Properties of lt for use in proofs *)
  lt_irrefl : forall x, ~ lt x x;
  lt_asymm : forall x y, lt x y -> ~ lt y x;
  lt_trans : forall x y z, lt x y -> lt y z -> lt x z;

  (* Properties of bounds, relating constants, operators, and functions *)
  le_succ_r : forall x y, le x y -> le x (succ y);
  le_pred_l : forall x y, le x y -> le (pred x) y;
  le_pred_lt : forall x y, lt MIN x -> le x (pred y) -> lt x y;
  lt_succ_le : forall x y, lt x MAX -> le (succ x) y -> lt x y;
}.

(* Type class instance *)
#[export] Instance byteBound : Bound byte := {
  MIN := byte_MIN;
  MAX := byte_MAX;
  pred := byte_pred;
  succ := byte_succ;
  eq := byte_eq;
  le := byte_le;
  lt := byte_lt;
  eq_dec := byte_eq_dec;
  le_dec := byte_le_dec;
  lt_dec := byte_lt_dec;
  eq_refl := byte_eq_refl;
  le_refl := byte_le_refl;
  le_antisymm := byte_le_antisymm;
  le_trans := byte_le_trans;
  lt_irrefl := byte_lt_irrefl;
  lt_asymm := byte_lt_asymm;
  lt_trans := byte_lt_trans;
  le_succ_r := byte_le_succ_r;
  le_pred_l := byte_le_pred_l;
  le_pred_lt := byte_le_pred_lt;
  lt_succ_le := byte_lt_succ_le;
}.
