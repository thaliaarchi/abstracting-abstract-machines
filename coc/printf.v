Require Import List Ascii String DecimalString.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Notation "x ::: y" := (String x y)
                            (at level 60, right associativity) : string_scope.

Definition show_nat (n : nat) : string :=
  DecimalString.NilZero.string_of_uint (Nat.to_uint n).

Module Lambda.

(** * [sprintf] with arguments via lambdas

    From example in paper “Cayenne — a language with dependent types” by Lennart
    Augustsson in 1998.

    It fails to typecheck, because Coq can't guess the decreasing argument and
    expects an incorrect type. *)

Fixpoint sprintf_type (fmt : string) : Type :=
  match fmt with
  | "%" ::: "d" ::: fmt' => nat -> sprintf_type fmt'
  | "%" ::: "s" ::: fmt' => string -> sprintf_type fmt'
  | _ ::: fmt' => sprintf_type fmt'
  | "" => string
  end.

Fail Program Fixpoint sprintf_ (fmt : string) (res : string) : sprintf_type fmt :=
  match fmt with
  | "%" ::: "d" ::: fmt' => fun n : nat => sprintf_ fmt' (res ++ show_nat n)
  | "%" ::: "s" ::: fmt' => fun s : string => sprintf_ fmt' (res ++ s)
  | a ::: fmt' => sprintf_ fmt' (res ++ a ::: "")
  | "" => res
  end.

Fail Definition sprintf (fmt : string) : sprintf_type fmt := sprintf_ fmt "".

End Lambda.
Module LambdaInductive.

(** * [sprintf] with arguments via lambdas and format parsed separately

    Idea from article “Type-safe printf in Coq” by Arthur Azevedo de Amorim in
    2013 (http://poleiro.info/posts/2013-04-19-type-safe-printf-in-coq.html) *)

Variant directive : Type :=
  | DLit (a : ascii)
  | DNat
  | DString.

Definition format : Type := list directive.

Fixpoint format_type (f : format) : Type :=
  match f with
  | DLit _ :: f' => format_type f'
  | DNat :: f' => nat -> format_type f'
  | DString :: f' => string -> format_type f'
  | [] => string
  end.

Fixpoint parse_format (s : string) : format :=
  match s with
  | "%" ::: "d" ::: s' => DNat :: parse_format s'
  | "%" ::: "s" ::: s' => DString :: parse_format s'
  | c ::: s' => DLit c :: parse_format s'
  | "" => []
  end.

Fixpoint sprintf_ (f : format) (res : string) : format_type f :=
  match f with
  | DLit a :: f' => sprintf_ f' (res ++ String a "")
  | DNat :: f' => fun n : nat => sprintf_ f' (res ++ show_nat n)
  | DString :: f' => fun s : string => sprintf_ f' (res ++ s)
  | [] => res
  end.

Definition sprintf (fmt : string) : format_type (parse_format fmt) :=
  sprintf_ (parse_format fmt) "".

Compute sprintf "Hello!".
Compute sprintf "Hello, %s!".
Compute sprintf "Hello, %s!" "world".
Compute sprintf "Hello, %d!" 42.
Fail Compute sprintf "Hello, %s!" 42.
Fail Compute sprintf "Hello, %s!" "world" 42.

End LambdaInductive.

Require Import ZArith ZifyClasses DecimalString.

Definition show_zify {A} `{InjTyp A Z} (x : A) : string :=
  DecimalString.NilZero.string_of_int (Z.to_int (inj x)).

Module Zify.

(** * [sprintf] with polymorphic numbers *)

Variant directive : Type :=
  | DLit (a : ascii)
  | DNum
  | DString.

Definition format : Type := list directive.

Fixpoint format_type (f : format) : Type :=
  match f with
  | DLit _ :: f' => format_type f'
  | DNum :: f' => forall A : Type, InjTyp A Z -> A -> format_type f'
  | DString :: f' => string -> format_type f'
  | [] => string
  end.

Fixpoint parse_format (s : string) : format :=
  match s with
  | "%" ::: "d" ::: s' => DNum :: parse_format s'
  | "%" ::: "s" ::: s' => DString :: parse_format s'
  | c ::: s' => DLit c :: parse_format s'
  | "" => []
  end.

Fixpoint sprintf_ (f : format) (res : string) : format_type f :=
  match f with
  | DLit a :: f' => sprintf_ f' (res ++ String a "")
  | DNum :: f' => fun A (H : InjTyp A Z) (x : A) => sprintf_ f' (res ++ show_zify x)
  | DString :: f' => fun s : string => sprintf_ f' (res ++ s)
  | [] => res
  end.

Definition sprintf (fmt : string) : format_type (parse_format fmt) :=
  sprintf_ (parse_format fmt) "".

(* Needs arguments for type and prop: *)
Compute sprintf "It's over %d!" _ _ 9000%Z.
Compute sprintf "Hello, %d!" _ _ (-42)%Z.
Compute sprintf "Hello, %d!" _ _ 42%N.
Compute sprintf "Hello, %d!" _ _ 42%positive.
Compute sprintf "Hello, %d!" _ _ 42%nat.

End Zify.
