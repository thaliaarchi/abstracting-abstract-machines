Require Import String.

Inductive name :=
  | Global : string -> name
  | Local : nat -> name
  | Quote : nat -> name.

Inductive typ :=
  | TFree : name -> typ
  | TFun : typ -> typ.

Inductive term_inf :=
  | Ann : term_chk -> typ -> term_inf
  | Bound : nat -> term_inf
  | Free : name -> term_inf
  | App : term_inf -> term_chk -> term_inf

with term_chk :=
  | Inf : term_inf -> term_chk
  | Lam : term_chk -> term_chk.

Inductive value :=
  (* | VLam : (value -> value) -> value *)
  | VNeutral : neutral -> value

with neutral :=
  | NFree : name -> neutral
  | NApp : neutral -> value -> neutral.
