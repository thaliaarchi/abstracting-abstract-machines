Require Import String.

(* Types *)
Inductive typ : Type :=
  | TyBool  : typ
  | TyArrow : typ -> typ -> typ.

(* Terms *)
Inductive term : Type :=
  | TmVar   : string -> term
  | TmApp   : term -> term -> term
  | TmLam   : string -> typ -> term -> term
  | TmTrue  : term
  | TmFalse : term
  | TmIf    : term -> term -> term -> term.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (TyArrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (TmApp x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (TmLam x t y) (in custom stlc at level 90, x at level 99,
                    t custom stlc at level 99,
                    y custom stlc at level 99,
                    left associativity).
Coercion TmVar : string >-> term.

Notation "'Bool'" := TyBool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (TmIf x y z) (in custom stlc at level 89,
                   x custom stlc at level 99,
                   y custom stlc at level 99,
                   z custom stlc at level 99,
                   left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := TmTrue (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := TmFalse (in custom stlc at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x y z : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Inductive value : term -> Prop :=
  | v_lam x T t : value <{\x:T, t}>
  | v_true : value <{true}>
  | v_false : value <{false}>.

Fixpoint subst (x : string) (s t : term) : term :=
  match t with
  | TmVar y => if String.eqb x y then s else t
  | <{\y:T, t1}> => if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> => <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end
  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).
