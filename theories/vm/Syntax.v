From Stdlib Require Import NArith.

Definition stack : Type := list N.
Definition pc : Type := N.

Inductive instr : Type :=
  | Const (n : N)
  | Pop
  | Add
  | Jmp (pos : pc)
  | Jnz (pos : pc).

Definition stmt_eqdec (st1 st2 : instr) : {st1=st2} + {st1<>st2}.
  repeat decide equality.
Defined.

Definition program : Type := list instr.