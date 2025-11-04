From Books Require Import Tactics.
From Books.vm Require Export Syntax.
From Stdlib Require Import List NArith Lia.
Import ListNotations.
Open Scope N_scope.

Fixpoint repeat {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => x :: repeat x n'
  end.

Definition list_update {X : Type} (default : X) (l : list X) (idx : N) (x : X) : list X :=
  let len := N.of_nat (length l) in
  let idx_nat := N.to_nat idx in
  let l' :=
    if len <=? idx then
      (* extend with default to the left so the target index exists *)
      repeat default (N.to_nat (idx - len) + 1) ++ l
    else l in
  let len' := length l' in
  let pos_from_left := (len' - 1 - idx_nat)%nat in
  firstn pos_from_left l' ++ [x] ++ skipn (S pos_from_left) l'.

Inductive step (p : program) : stack -> pc -> stack -> pc -> Prop :=
| SConst : forall n st pc,
    p pc = Some (Const n) ->
    step p st pc (n :: st) (pc + 1)
| SPop : forall n st pc,
    p pc = Some Pop ->
    step p (n :: st) pc st (pc + 1)
| SPlus : forall n1 n2 st pc,
    p pc = Some Plus ->
    step p (n2 :: n1 :: st) pc (n1 + n2 :: st) (pc + 1)
| SMinus : forall n1 n2 st pc,
    p pc = Some Minus ->
    step p (n2 :: n1 :: st) pc (n1 - n2 :: st) (pc + 1)
| SDup : forall idx n st pc,
    p pc = Some Dup ->
    nth_error st (length st - N.to_nat idx - 1) = Some n ->
    step p (idx :: st) pc (n :: st) (pc + 1)
| SSwap : forall n1 n2 st pc,
    p pc = Some Swap ->
    step p (n1 :: n2 :: st) pc (n2 :: n1 :: st) (pc + 1)
| STop : forall st pc,
    p pc = Some Top ->
    step p st pc (N.of_nat (length st) :: st) (pc + 1)
| SStore : forall idx n st pc,
    p pc = Some Store ->
    step p (n :: idx :: st) pc (list_update 0 st (N.of_nat (length st) - idx) n) (pc + 1)
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

Inductive exec_prog (p : program) : stack -> pc -> stack -> pc -> Prop :=
| ExecDone : forall st pc,
    p pc = None ->
    exec_prog p st pc st pc
| ExecStep : forall st1 st2 pc1 pc2 st3 pc3,
    p pc1 <> None ->
    (* One step of execution *)
    step p st1 pc1 st2 pc2 ->
    (* Continue executing *)
    exec_prog p st2 pc2 st3 pc3 ->
    exec_prog p st1 pc1 st3 pc3.

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
  all: inv H; solve_ppc; inv H0; solve_ppc; try easy.
Qed.

Theorem exec_prog_deterministic :
  forall p st pc st1' pc1' st2' pc2',
    exec_prog p st pc st1' pc1' ->
    exec_prog p st pc st2' pc2' ->
    st1' = st2' /\ pc1' = pc2'.
Proof.
  intros. induction H.
  - (* Terminated *) inv H0. easy. contradiction.
  - (* Continue *) inv H0. contradiction. clear H3.
      pose proof (step_deterministic _ _ _ _ _ _ _ H1 H4). destruct H0; subst.
      apply IHexec_prog. assumption.
Qed.

Lemma exec_prog_no_step :
  forall p st pc st1 pc1,
    exec_prog p st pc st1 pc1 ->
    ~ exists st1' pc1', step p st1 pc1 st1' pc1'.
Proof.
  intros. induction H.
  - intro. destruct H0 as (st' & pc' & Step). inv Step; rewrite H in H0; inv H0.
  - apply IHexec_prog.
Qed.