From Stdlib Require Export NArith.
From Stdlib Require Export String.

Definition ident := string.
Definition ieqb := String.eqb.

Inductive Aexpr :=
  | ConstNat (n : N)
  | VarNat (i : ident)
  | Plus (e1 e2 : Aexpr)
  | Minus (e1 e2 : Aexpr)
  | Mult (e1 e2 : Aexpr).

Inductive Bexpr :=
  | ConstBool (b : bool)
  | VarBool (i : ident)
  | Neg (e : Bexpr)
  | Or (e1 e2 : Bexpr)
  | And (e1 e2 : Bexpr).

Inductive expr :=
  | AE (a : Aexpr)
  | BE (b : Bexpr).

Inductive storeval : Type := Nat (n : N) | Bool (b : bool).

Definition store : Type := ident -> option storeval.

Definition update {A B : Type} (eqb : A -> A -> bool) (s : A -> B) (k : A) (v : B) :=
  fun k' => if eqb k k' then v else s k'.
Definition supdate : store -> ident -> option storeval -> store := update ieqb.

Inductive stmt : Type :=
  | Skip
  | Seq (s1 s2 : stmt)
  | Assign (id : ident) (e : expr)
  | IfThenElse (b : Bexpr) (s1 s2 : stmt)
  | While (b : Bexpr) (body : stmt).

Definition stmt_eqdec (st1 st2 : stmt) : {st1=st2} + {st1<>st2}.
  repeat decide equality.
Defined.
