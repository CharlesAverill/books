From Books Require Import Tactics.
From Books.vm Require Import Syntax.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Inductive step (p : program) : stack -> pc -> stack -> pc -> Prop :=
| SConst : forall n st pc,
    p pc = Some (Const n) ->
    step p st pc (n :: st) (pc + 1)
| SPop : forall n st pc,
    p pc = Some Pop ->
    step p (n :: st) pc st (pc + 1)
| SPlus : forall n1 n2 st pc,
    p pc = Some Plus ->
    step p (n1 :: n2 :: st) pc (n1 + n2 :: st) (pc + 1)
| SJmp : forall pc' st pc,
    p pc = Some (Jmp pc') ->
    step p st pc st pc'
| SJnzT : forall n pc' st pc,
    p pc = Some (Jnz pc') ->
    0 < n ->
    step p (n :: st) pc (n :: st) pc'
| SJnzF : forall pc' st pc,
    p pc = Some (Jnz pc') ->
    step p (0 :: st) pc (0 :: st) (pc + 1).

Hint Constructors step : core.

Ltac solve_ppc :=
  match goal with
  | [H: ?p ?pc = Some ?x, H0: ?p ?pc = Some ?y |- _] => rewrite H in H0; inv H0
  end.

Theorem step_deterministic :
  forall p st pc st1' pc1' st2' pc2',
    step p st pc st1' pc1' ->
    step p st pc st2' pc2' ->
    st1' = st2' /\ pc1' = pc2'.
Proof.
  intros. assert (p pc = None \/ exists instr, p pc = Some instr). {
    destruct (p pc). right. now exists i. now left.
  } destruct H1. exfalso. inv H; rewrite H1 in H2; discriminate.
  destruct H1 as (I & PPCI). revert st1' pc1' st2' pc2' p pc st PPCI H H0.
  destruct I; intros.
  all: inv H; solve_ppc; inv H0; solve_ppc; easy.
Qed.