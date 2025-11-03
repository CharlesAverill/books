From Books Require Import compiler.Layout.
From Books Require Import lang.Syntax vm.Syntax vm.FInterp vm.Semantics.
From Stdlib Require Import List.
Import ListNotations.

Definition LOAD (l : var_layout) (i : ident) : list instr := [Const (l i); Dup].

Definition GETN (n : N) : list instr :=
  [ Top; Const n; Minus; Dup ].

Definition SETN (n : N) (val : N) : list instr :=
  [ Top; Const n; Minus; Const 1; Plus; Const val; Store ].

Definition SETN_fromstack (n : N) : list instr :=
  [ Top; Const n; Minus; Const 1; Minus; Swap; Store ].

Definition MULT (pc : N) : list instr :=
  [
    (* init acc = 0 *)
    Const 0                         (* 0 :: b :: a :: st *)
  ] ++
    (* loop_start: pc + 1 *)
    GETN 1                          (* duplicate b *)
  ++ [
    Jnz (pc + 7);                   (* if b != 0 jump to loop_body *)
    Jmp (pc + 27);                    (* else jump to done *)
    Pop
  ] ++
    (* loop_body: pc + 7 *)
    GETN 2                          (* duplicate a *)
  ++ [
    Plus                            (* acc := acc + a *)
  ] ++
    (* decrement b *)
    GETN 1
  ++ [
    Const 1; Minus
  ] ++ SETN_fromstack 1 ++ [
    Jmp (pc + 1);                   (* loop *)

    (* done: pc + 25 *)
    Pop; Swap; Pop; Swap; Pop
  ].

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