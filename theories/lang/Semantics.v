From Books Require Import Tactics.
From Books.lang Require Import Syntax.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.
Open Scope bool.

Definition _compute_arith_bop op : option N :=
  match op with
  | Plus (ConstNat n1) (ConstNat n2) => Some (n1 + n2)
  | Minus (ConstNat n1) (ConstNat n2) => Some (n1 - n2)
  | Mult (ConstNat n1) (ConstNat n2) => Some (n1 * n2)
  | _ => None
  end.

Inductive aeval : store -> Aexpr -> N -> Prop :=
  | EVarConst s n :
      aeval s (ConstNat n) n
  | EVarNat s i v :
      s i = Some (Nat v) ->
      aeval s (VarNat i) v
  | EABop s op a1 a2 n1 n2 v :
      In op [Plus; Minus; Mult] -> aeval s a1 n1 -> aeval s a2 n2 ->
      _compute_arith_bop (op (ConstNat n1) (ConstNat n2)) = Some v ->
      aeval s (op a1 a2) v.

Definition _compute_bool_op op : option bool :=
  match op with
  | Neg (ConstBool b) => Some (negb b)
  | Or (ConstBool b1) (ConstBool b2) => Some (b1 || b2)
  | And (ConstBool b1) (ConstBool b2) => Some (b1 && b2)
  | _ => None
  end.

Inductive beval : store -> Bexpr -> bool -> Prop :=
  | EConstBool s b :
      beval s (ConstBool b) b
  | EVarBool s i v :
      s i = Some (Bool v) ->
      beval s (VarBool i) v
  | EBUop s op e b v :
      In op [Neg] -> beval s e b ->
      _compute_bool_op (op (ConstBool b)) = Some v ->
      beval s (op e) v
  | EBBop s (op : Bexpr -> Bexpr -> Bexpr) a1 a2 b1 b2 v :
      In op [Or; And] -> beval s a1 b1 -> beval s a2 b2 ->
      _compute_bool_op (op (ConstBool b1) (ConstBool b2)) = Some v ->
      beval s (op a1 a2) v.

Inductive eeval : store -> expr -> storeval -> Prop :=
  | SAE s a a' : aeval s a a' -> eeval s (AE a) (Nat a')
  | SBE s b b' : beval s b b' -> eeval s (BE b) (Bool b').

Inductive step : store -> stmt -> store -> stmt -> Prop :=
  | SSeq c1 c1' c2 s s' :
      step s c1 s' c1' ->
      step s (Seq c1 c2) s' (Seq c1' c2)
  | SSkipSeq c s :
      step s (Seq Skip c) s c
  | SAssign i e v s :
      eeval s e v ->
      step s (Assign i e) (update s i (Some v)) Skip
  | SIfTrue s b c1 c2 :
      beval s b true ->
      step s (IfThenElse b c1 c2) s c1
  | SIfFalse s b c1 c2 :
      beval s b false ->
      step s (IfThenElse b c1 c2) s c2
  | SWhile s b c :
      step s (While b c) s (IfThenElse b (Seq c (While b c)) Skip).

Hint Constructors step : core.

Ltac solve_in :=
  repeat match goal with
  | [H: In _ [] |- _ ] => inv H
  | [H: In ?op _ |- _] => inv H; [easy|]
  end.

Lemma aeval_deterministic :
  forall s a v1 v2,
    aeval s a v1 -> aeval s a v2 -> v1 = v2.
Proof.
  induction a; intros.
  - (* ConstNat *) inv H. inv H0. reflexivity. solve_in. solve_in.
  - (* VarNat *) inv H. inv H0. destruct (s i); try discriminate.
      inv H2. inv H3. reflexivity. solve_in. solve_in.
  - (* Plus *) inv H. inv H0.
      replace op with Plus in * by solve_in. replace op0 with Plus in * by solve_in.
      inv H1. inv H. simpl in H6, H10. inv H6. inv H10.
      enough (n1 = n0 /\ n2 = n3). destruct H; now subst. auto.
  - (* Minus *) inv H. inv H0.
      replace op with Minus in * by solve_in. replace op0 with Minus in * by solve_in.
      inv H1. inv H. simpl in H6, H10. inv H6. inv H10.
      enough (n1 = n0 /\ n2 = n3). destruct H; now subst. auto.
  - (* Mult *) inv H. inv H0.
      replace op with Mult in * by solve_in. replace op0 with Mult in * by solve_in.
      inv H1. inv H. simpl in H6, H10. inv H6. inv H10.
      enough (n1 = n0 /\ n2 = n3). destruct H; now subst. auto.
Qed.

Lemma beval_deterministic :
  forall s b v1 v2,
    beval s b v1 -> beval s b v2 -> v1 = v2.
Proof.
  induction b; intros.
  - (* ConstBool *) inv H. inv H0. reflexivity. all: solve_in.
  - (* VarBool *) inv H. inv H0. rewrite H2 in H3. now inv H3. all: solve_in.
  - (* Neg *) inv H; solve_in. inv H0; solve_in.
      replace op with Neg in * by solve_in.
      replace op0 with Neg in * by solve_in.
      simpl in H5, H8. inv H8. inv H5.
      inv H1. inv H. f_equal. auto.
  - (* Or *) inv H; solve_in. inv H0; solve_in.
      replace op with Or in * by solve_in.
      replace op0 with Or in * by solve_in.
      inv H1. inv H. simpl in H6, H10. inv H6. inv H10.
      enough (b0 = b4 /\ b3 = b5). destruct H. now subst. auto.
  - (* And *) inv H; solve_in. inv H0; solve_in.
      replace op with And in * by solve_in.
      replace op0 with And in * by solve_in.
      inv H1. inv H2. simpl in H6, H10. inv H6. inv H10.
      enough (b0 = b4 /\ b3 = b5). destruct H1. now subst. auto.
Qed.

Lemma eeval_deterministic :
  forall s e v1 v2,
    eeval s e v1 -> eeval s e v2 -> v1 = v2.
Proof.
  induction e; intros; inv H; inv H0.
  - f_equal. eauto using aeval_deterministic.
  - f_equal. eauto using beval_deterministic.
Qed.

Theorem step_deterministic :
  forall s st s1' s2' st1 st2,
    step s st s1' st1 -> step s st s2' st2 -> s1' = s2' /\ st1 = st2.
Proof.
  induction st; intros.
  - (* Skip *) inv H.
  - (* Seq *) inv H. inv H0.
    specialize (IHst1 _ _ _ _ H5 H6). destruct IHst1; subst. easy.
    inv H6. inv H0. inv H5. easy.
  - (* Assign *)
    inv H. inv H0. pose proof (eeval_deterministic _ _ _ _ H5 H6). subst. easy.
  - (* IfThenElse *)
    inv H.
    -- inv H0. easy.
       enough (eeval s2' (BE b) (Bool true) /\ eeval s2' (BE b) (Bool false)).
       destruct H. pose proof (eeval_deterministic _ _ _ _ H H0). inv H1.
       split; constructor; assumption.
    -- inv H0.
       enough (eeval s2' (BE b) (Bool true) /\ eeval s2' (BE b) (Bool false)).
       destruct H. pose proof (eeval_deterministic _ _ _ _ H H0). inv H1.
       split; constructor; assumption. easy.
  - (* While *)
    inv H. inv H0. easy.
Qed.