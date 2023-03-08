Require Import List Ascii String DecimalString.
Local Open Scope string_scope.
Local Notation "x ::: y" := (String x y)
                            (at level 60, right associativity) : string_scope.

(** * Cayenne-style sprintf

    Printf example from “Cayenne — a language with dependent types” (Augustsson
    1998).

    It fails to typecheck. *)

Fixpoint sprintf_type (fmt : string) : Type :=
  match fmt with
  | "%" ::: "d" ::: fmt' => nat -> sprintf_type fmt'
  | "%" ::: "s" ::: fmt' => string -> sprintf_type fmt'
  | _ ::: fmt' => sprintf_type fmt'
  | "" => string
  end.

Definition show_nat (n : nat) : string :=
  DecimalString.NilZero.string_of_uint (Nat.to_uint n).

Fail Program Fixpoint sprintf_ (fmt : string) (res : string) : sprintf_type fmt :=
  match fmt with
  | "%" ::: "d" ::: fmt' => fun n : nat => sprintf_ fmt' (res ++ show_nat n)
  | "%" ::: "s" ::: fmt' => fun s : string => sprintf_ fmt' (res ++ s)
  | a ::: fmt' => sprintf_ fmt' (res ++ a ::: "")
  | "" => res
  end.

Fail Definition sprintf (fmt : string) : sprintf_type fmt := sprintf_ fmt "".
