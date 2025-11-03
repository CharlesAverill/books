From Books.vm Require Import Syntax Semantics.
From Books Require Import Tactics.
From Stdlib Require Import NArith List Lia.
Import ListNotations.

Definition fstep (p : program) (st : stack) (pcnt : pc) : option (stack * pc) :=
  match p pcnt with
  | Some (Const n) => Some (n :: st, pcnt + 1)
  | Some Pop =>
      match st with
      | [] => None
      | h :: t => Some (t, pcnt + 1)
      end
  | Some Plus =>
      match st with
      | n :: m :: t => Some (n + m :: t, pcnt + 1)
      | _ => None
      end
  | Some (Jmp pcnt') => Some (st, pcnt')
  | Some (Jnz pcnt') =>
      match st with
      | x :: t => Some (st, if x =? 0 then pcnt + 1 else pcnt')
      | _ => None
      end
  | _ => None
  end.

Section FInterpCorrectness.

Theorem fstep_sound :
  forall p st pc st' pc',
    fstep p st pc = Some (st', pc') ->
    step p st pc st' pc'.
Proof.
  intros. assert (p pc = None \/ exists instr, p pc = Some instr). {
    destruct (p pc). right. now exists i. now left.
  } destruct H0. unfold fstep in H. rewrite H0 in H. discriminate.
  destruct H0 as (I & PPCI). destruct I.
  all: unfold fstep in H; rewrite PPCI in H; inv H.
  - (* Const *) now constructor.
  - (* Pop *) destruct st; inv H1. now constructor.
  - (* Plus *) destruct st; inv H1; destruct st; inv H0. now constructor.
  - (* Jmp *) now constructor.
  - (* Jnz *) destruct st; inv H1. destruct (n =? 0) eqn:E.
      replace n with 0 in *. eauto. apply N.eqb_eq in E. now subst.
      apply SJnzT. assumption. apply N.eqb_neq in E. lia.
Qed.

Theorem fstep_complete :
  forall p st pc st' pc',
    step p st pc st' pc' ->
    fstep p st pc = Some (st', pc').
Proof.
  intros. induction H; unfold fstep; rewrite H; clear H; auto.
  destruct (n =? 0) eqn:E.
    apply N.eqb_eq in E. lia.
    reflexivity.
Qed.

End FInterpCorrectness.