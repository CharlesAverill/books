From Books Require Import compiler.Routines compiler.Layout.
From Books Require Import lang.Syntax vm.Syntax vm.FInterp.
From Stdlib Require Import List.
Import ListNotations.

Definition LN {X : Type} := fun (x : list X) => N.of_nat (List.length x).

Fixpoint AEVAL (pc : pc) (l : var_layout) (a : Aexpr) : list instr :=
  match a with
  | ConstNat n => [Const n]
  | VarNat i => LOAD l i
  | lang.Syntax.Plus a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + LN l1) l a2
      in l1 ++ l2 ++ [Plus]
  | lang.Syntax.Minus a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + LN l1) l a2
      in l1 ++ l2 ++ [Minus]
  | lang.Syntax.Mult a1 a2 =>
      let l1 := AEVAL pc l a1 in
      let l2 := AEVAL (pc + LN l1) l a2
      in l1 ++ l2 ++ MULT (pc + LN l1 + LN l2)
  end.

Fixpoint BEVAL (pc : pc) (l : var_layout) (b : Bexpr) : list instr :=
  match b with
  | ConstBool b => [Const (if b then 1 else 0)]
  | VarBool i => LOAD l i
  | lang.Syntax.Neg b =>
      let l1 := BEVAL pc l b in
      l1 ++ NEG (pc + LN l1)
  | lang.Syntax.Or b1 b2 =>
      let l1 := BEVAL pc l b1 in
      let l2 := BEVAL (pc + N.of_nat (length l1)) l b2
      in l1 ++ l2 ++ OR (pc + LN l1 + LN l2)
  | lang.Syntax.And b1 b2 =>
      let l1 := BEVAL pc l b1 in
      let l2 := BEVAL (pc + N.of_nat (length l1)) l b2
      in l1 ++ l2 ++ AND (pc + LN l1 + LN l2)
  end.

Fixpoint CEVAL (pc : pc) (l : var_layout) (c : stmt) : list instr :=
  match c with
  | Skip => []
  | Assign i e =>
      let le := match e with AE e => AEVAL pc l e | BE e => BEVAL pc l e end in
      le ++ SETN_fromstack (l i)
  | Seq c1 c2 =>
      let lc1 := CEVAL pc l c1 in
      let lc2 := CEVAL (pc + LN lc1) l c2 in
      lc1 ++ lc2
  | IfThenElse b c1 c2 =>
      let lb := BEVAL pc l (Neg b) in
      let lc1 := CEVAL (pc + LN lb) l c1 in
      let lc2 := CEVAL (pc + LN lb + LN lc1) l c2 in
      lb ++ [Jnz (pc + LN lb + 1 + LN lc1 + 1)]
         ++ lc1
         ++ [Jmp (pc + LN lb + 1 + LN lc1 + 1 + LN lc2)]
         ++ lc2
  | While b cbody =>
      let lb := BEVAL pc l b in
      let lcbody := CEVAL (pc + N.of_nat (length lb) + 2) l cbody in
      lb ++ [Jnz (pc + N.of_nat (length lb) + 2)]
         ++ lcbody
         ++ [Jmp pc]
  end.

Require Import String.
Open Scope string.
Definition plist := CEVAL 0 (fun _ => 0) (IfThenElse (ConstBool true) (Assign "hello" (AE (ConstNat 99))) Skip).
Definition prog := program_of_plist plist.

Compute fmultistep prog [] 0 (LN plist) 30.
