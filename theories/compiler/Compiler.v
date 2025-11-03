From Books Require Import compiler.Routines compiler.Layout.
From Books Require Import lang.Syntax vm.Syntax.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint AEVAL (pc : pc) (l : var_layout) (a : Aexpr) : list instr :=
  match a with
  | ConstNat n => [Const n]
  | VarNat i => LOAD l i
  | lang.Syntax.Plus a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + N.of_nat (length l1)) l a2
      in l1 ++ l2 ++ [Plus]
  | lang.Syntax.Minus a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + N.of_nat (length l1)) l a2
      in l1 ++ l2 ++ [Minus]
  | lang.Syntax.Mult a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + N.of_nat (length l1)) l a2
      in l1 ++ l2 ++ MULT (pc + N.of_nat (length l1) + N.of_nat (length l2))
  end.

Fixpoint BEVAL (pc : pc) (l : var_layout) (b : Bexpr) : list instr :=
  match b with
  | ConstBool b => [Const (if b then 1 else 0)]
  | VarBool i => LOAD l i
  | lang.Syntax.Neg b =>
      let l1 := BEVAL pc l b in
      l1 ++ NEG (pc + N.of_nat (length l1))
  | lang.Syntax.Or b1 b2 =>
      let l1 := BEVAL pc l b1 in
      let l2 := BEVAL (pc + N.of_nat (length l1)) l b2
      in l1 ++ l2 ++ OR (pc + N.of_nat (length l1) + N.of_nat (length l2))
  | lang.Syntax.And b1 b2 =>
      let l1 := BEVAL pc l b1 in
      let l2 := BEVAL (pc + N.of_nat (length l1)) l b2
      in l1 ++ l2 ++ AND (pc + N.of_nat (length l1) + N.of_nat (length l2))
  end.