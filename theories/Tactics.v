From Stdlib Require Import NArith Lia ZifyN ZifyBool List.
Import ListNotations.
Open Scope N_scope.

Ltac inv H := inversion H; subst; clear H.

Ltac eqb_false :=
  match goal with [|- context[?x =? ?y]] => replace (x =? y) with false by lia end.
Ltac eqb_true :=
  match goal with [|- context[?x =? ?y]] => replace (x =? y) with true by lia end.
Ltac eqb_hammer := repeat (eqb_false || eqb_true).

Ltac solve_in :=
  repeat match goal with
  | [H: In _ [] |- _ ] => inv H
  | [H: In ?op _ |- _] => inv H; [easy|]
  end.