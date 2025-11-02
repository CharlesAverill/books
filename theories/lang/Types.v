Require Import BSyntax.

Inductive btype : Set :=
  | TNat
  | TBool.

Definition typctx : Type := ident -> option btype.

Inductive expr_hastype : expr -> btype -> Prop :=
  | AET a : expr_hastype (AE a) TNat
  | BET b : expr_hastype (BE b) TBool.