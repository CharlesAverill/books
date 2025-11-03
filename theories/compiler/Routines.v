From Books Require Import compiler.Layout.
From Books Require Import lang.Syntax vm.Syntax.
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

Definition NEG (pc : N) : list instr :=
  [ Jnz (pc + 4); Pop; Const 1; Jmp (pc + 6); Pop; Const 0 ].

Definition OR (pc : N) : list instr :=
  [ Jnz (pc + 6); Pop; Jnz (pc + 7); Pop; Const 0; Jmp (pc + 9); Pop; Pop; Const 1 ].

Definition AND (pc : N) : list instr :=
  [ Jnz (pc + 5); Pop; Pop; Const 0; Jmp (pc + 11);
    Pop; Jnz (pc + 9); Pop; Const 0; Jmp (pc + 11);
    Pop; Pop; Const 1
  ].