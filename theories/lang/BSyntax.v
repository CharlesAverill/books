From Stdlib Require Export NArith.
From Stdlib Require Export String.

Definition ident := string.
Definition ieqb := String.eqb.

Inductive Aexpr :=
  | ConstNat (n : N)
  | VarNat (i : ident)
  | Plus (e1 e2 : Aexpr)
  | Minus (e1 e2 : Aexpr)
  | Mult (e1 e2 : Aexpr)
  | Div (e1 e2 : Aexpr).

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

Definition update (s : store) k v := fun k' => if ieqb k k' then v else s k'.

Inductive stmt : Type :=
  | Skip
  | Seq (s1 s2 : stmt)
  | Assign (id : ident) (e : expr)
  | IfThenElse (b : Bexpr) (s1 s2 : stmt)
  | While (b : Bexpr) (body : stmt).

Definition stmt_eqdec (st1 st2 : stmt) : {st1=st2} + {st1<>st2}.
  repeat decide equality.
Defined.
