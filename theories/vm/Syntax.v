From Stdlib Require Import NArith List.
Open Scope N_scope.

Definition stack : Type := list N.
Definition pc : Type := N.

Inductive instr : Type :=
  | Const (n : N)
  | Pop
  | Plus
  | Minus
  | Top
  | Dup
  | Swap
  | Store
  | Jmp (pos : pc)
  | Jnz (pos : pc).

Definition stmt_eqdec (st1 st2 : instr) : {st1=st2} + {st1<>st2}.
  repeat decide equality.
Defined.

Definition program : Type := pc -> option instr.

Definition plist : Type := list instr.
Definition program_of_plist (pl : plist) : program :=
  snd (fold_left (
    fun a i =>
      match a with
      | (pc, prog) => (pc + 1, fun pc' => if pc' =? pc then Some i else prog pc')
      end
  ) pl (0, (fun _ => None))).