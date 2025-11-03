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
      | m :: n :: t => Some (n + m :: t, pcnt + 1)
      | _ => None
      end
  | Some Minus =>
      match st with
      | m :: n :: t => Some (n - m :: t, pcnt + 1)
      | _ => None
      end
  | Some Dup =>
      match st with
      | idx :: st' =>
          match nth_error st' (length st' - N.to_nat idx) with
          | Some n => Some (n :: st', pcnt + 1)
          | _ => None
          end
      | _ => None
      end
  | Some Swap =>
      match st with
      | n1 :: n2 :: st' => Some (n2 :: n1 :: st', pcnt + 1)
      | _ => None
      end
  | Some Store =>
      match st with
      | n :: idx :: t => Some (list_update t (N.of_nat (length t) - idx) n, pcnt + 1)
      | _ => None
      end
  | Some Top => Some (N.of_nat (length st) :: st, pcnt + 1)
  | Some (Jmp pcnt') => Some (st, pcnt')
  | Some (Jnz pcnt') =>
      match st with
      | x :: t => Some (st, if x =? 0 then pcnt + 1 else pcnt')
      | _ => None
      end
  | _ => None
  end.

Fixpoint fmultistep (p : program) (st : stack) (pcnt : pc) (len : N) (fuel : nat) :=
  match fuel with
  | O => Some (st, pcnt)
  | S fuel' =>
      if pcnt <? len then
        match fstep p st pcnt with
        | Some (st', pcnt') => fmultistep p st' pcnt' len fuel'
        | _ => Some (st, pcnt)
        end
      else Some (st, pcnt)
  end.

Definition frun (p : program) (len : N) (fuel : nat) := fmultistep p [] 0 len fuel.

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
  - (* Pop *) destruct st; inv H1; now constructor.
  - (* Plus *) destruct st; inv H1; destruct st; inv H0; now constructor.
  - (* Minus *) destruct st; inv H1; destruct st; inv H0; now constructor.
  - (* Top *) now constructor.
  - (* Dup *) destruct st as [|idx st]; inv H1.
      destruct (nth_error st (length st - N.to_nat idx)) eqn:E; inv H0; eauto.
  - (* Swap *) destruct st; inv H1; destruct st; inv H0; now constructor.
  - (* Store *) destruct st; inv H1; destruct st; inv H0; now constructor.
  - (* Jmp *) now constructor.
  - (* Jnz *) destruct st; inv H1. destruct (n =? 0) eqn:E.
      replace n with 0 in *; eauto. apply N.eqb_eq in E; now subst.
      apply SJnzT. assumption. apply N.eqb_neq in E. lia.
Qed.

Theorem fstep_complete :
  forall p st pc st' pc',
    step p st pc st' pc' ->
    fstep p st pc = Some (st', pc').
Proof.
  intros. induction H; unfold fstep; rewrite H; clear H; auto.
  - (* Dup *)
      rewrite H0. reflexivity.
  - (* Jnz *)
      destruct (n =? 0) eqn:E.
        apply N.eqb_eq in E. lia.
        reflexivity.
Qed.

End FInterpCorrectness.