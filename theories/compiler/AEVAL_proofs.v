From Books Require Import compiler.Compiler vm.Semantics lang.Semantics Tactics.
From Stdlib Require Import List Lia Nat.
Import ListNotations.

Definition N_of_storeval (s : storeval) : N :=
  match s with
  | Nat n => n
  | Bool b => if b then 1 else 0
  end.

Definition mem_models_store (l : layout) (st : stack) (s : store) :=
  forall i v,
    s i = Some v <-> 
      (exists idx, l i = Some idx /\
       nth_error st (length st - N.to_nat idx - 1) = Some (N_of_storeval v)).

Lemma nth_error_some_idx_valid :
  forall {A} (l : list A) i v,
    nth_error l i = Some v ->
    (i < length l)%nat.
Proof.
  induction l; intros.
  - rewrite nth_error_nil in H. inv H.
  - rewrite nth_error_cons in H. destruct i. inv H. simpl. lia.
      simpl. apply Arith_base.lt_n_S_stt. eauto.
Qed.

Lemma fold_left_cons :
  forall {A B} f (h : A) t (i : B),
    fold_left f (h :: t) i = fold_left f t (f i h).
Proof. reflexivity. Qed.

Lemma program_of_plist_exact :
  forall t pc h,
    program_of_plist pc (h :: t) pc = Some h.
Admitted.

Lemma exec_prog_cons :
  forall h t st pc st' pc' st'' pc'',
    vm.Semantics.step (program_of_plist pc [h]) st pc st' pc' ->
    exec_prog (program_of_plist pc (h :: t)) st' pc' st'' pc'' ->
    exec_prog (program_of_plist pc (h :: t)) st pc st'' pc''.
Proof.
  intros. unfold program_of_plist in H. simpl in H.
  inv H; rewrite N.eqb_refl in H1; inv H1.
  all: try solve [econstructor; [
      now rewrite program_of_plist_exact
    | constructor; (apply program_of_plist_exact || eassumption)
    | assumption]].
  econstructor.
    now rewrite program_of_plist_exact.
    eapply SJnzF. apply program_of_plist_exact. assumption.
Qed.

(* Lemma step_trans :
  forall l1 l2 st pc st' pc' st'' pc'',
    vm.Semantics.step (program_of_plist pc l1) st pc st' pc' ->
    vm.Semantics.step (program_of_plist pc (l1 ++ l2)) st pc st'' pc''.
Proof.
  induction l1; intros.
  - unfold program_of_plist in H; simpl in H. inv H; inv H0.
  - simpl. inv H; rewrite program_of_plist_exact in H0; inv H0. *)

Lemma exec_prog_trans :
  forall l1 l2 st pc st' pc' st'' pc'',
    exec_prog (program_of_plist pc l1) st pc st' pc' ->
    exec_prog (program_of_plist pc' l2) st' pc' st'' pc'' ->
    exec_prog (program_of_plist pc (l1 ++ l2)) st pc st'' pc''.
Admitted.

Lemma models_store_cons :
  forall l st s h,
    mem_models_store l st s ->
    mem_models_store l (h :: st) s.
Admitted.
(* Proof.
  induction l; intros.
  - unfold mem_models_store. intros. specialize (H i v). destruct H.
    split; intro.
    -- specialize (H H1). destruct H as (idx & Eq & Lt & Err). eexists. split. eassumption.
       split. simpl length. rewrite Nat2N.inj_succ, <- N.add_1_r. lia.
       simpl length. rewrite <- PeanoNat.Nat.sub_add_distr, PeanoNat.Nat.add_comm. simpl.
       replace (Datatypes.length st - N.to_nat idx)%nat with (S (Datatypes.length st - N.to_nat idx - 1)).
       rewrite nth_error_cons_succ. apply Err.
       rewrite <- PeanoNat.Nat.sub_add_distr, PeanoNat.Nat.add_comm. simpl.
       rewrite <- PeanoNat.Nat.sub_succ_l, PeanoNat.Nat.sub_succ. reflexivity. lia.
    -- destruct H1 as (idx & Eq & Lt & Err). apply H0. exists idx. split. assumption.
       split. simpl length in Lt. rewrite Nat2N.inj_succ, <- N.add_1_r in Lt.
       destruct (N.eq_dec idx (N.of_nat (length st))). subst idx.
       rewrite Nat2N.id in Err. simpl length in Err.
       rewrite <- PeanoNat.Nat.sub_add_distr, PeanoNat.Nat.add_comm in Err. simpl in Err.
       rewrite PeanoNat.Nat.sub_diag in Err. simpl in Err. inv Err. *)

Lemma of_nat_length_LN : forall {A} (l : list A),
  N.of_nat (length l) = LN l.
Proof. reflexivity. Qed.

Lemma LN_app : forall {A} (l1 l2 : list A),
  LN l1 + LN l2 = LN (l1 ++ l2).
Proof.
  induction l1; intros.
  - reflexivity.
  - unfold LN in *. simpl length. repeat rewrite Nat2N.inj_succ. rewrite <- IHl1. lia.
Qed.

Lemma LN_app_cons : forall {A} (l : list A) (x : A),
  LN (l ++ [x]) = LN l + 1.
Proof.
  intros. rewrite <- LN_app. reflexivity.
Qed.

Theorem AEVAL_correct :
  forall a l s n pc st,
    mem_models_store l st s ->
    aeval s a n ->
    exec_prog (program_of_plist pc (AEVAL pc l a))
      st pc 
      (n :: st) (pc + N.of_nat (length (AEVAL pc l a))).
Proof.
  induction a; intros.
  - (* ConstNat *) unfold program_of_plist; simpl.
        econstructor.
          rewrite N.eqb_refl. discriminate.
          constructor. now rewrite N.eqb_refl.
          inv H0.
            constructor. now eqb_hammer.
            solve_in.
  - (* VarNat *)
    unfold program_of_plist; simpl; unfold LOAD.
    destruct (l i) eqn:E; simpl.
    -- econstructor.
         eqb_hammer. discriminate.
         constructor. now eqb_hammer.
         inv H0.
           econstructor.
             now eqb_hammer. {
             apply SDup. now eqb_hammer.
             specialize (H i (Nat n)). rewrite E, H3 in H. destruct H as (L & R).
             specialize (L ltac:(eauto)).
             destruct st.
              exfalso. destruct L, H. rewrite nth_error_nil in H0. inv H0.
              apply nth_error_nth'. rewrite length_cons. lia.
           } { replace (pc + 1 + 1) with (pc + 2) by lia.
             specialize (H i (Nat n)). rewrite E, H3 in H. destruct H. specialize (H eq_refl).
             replace (nth _ st _) with n. constructor.
             now eqb_hammer.
             destruct H as (idx & Eq & Err). inv Eq.
             eapply nth_error_nth in Err. now rewrite Err.
           } solve_in.
    -- inv H0. specialize (H i (Nat n)). destruct H. specialize (H H3). destruct H as (idx & Eq & Err).
       rewrite E in Eq. discriminate. solve_in.
  - (* Plus *)
    simpl AEVAL. inv H0. replace op with Plus in * by solve_in. inv H1.
      eapply exec_prog_trans. eauto.
      eapply exec_prog_trans. eapply IHa2. apply models_store_cons. eassumption. eassumption.
      econstructor. now rewrite program_of_plist_exact.
      constructor; now rewrite program_of_plist_exact.
      simpl in H6. inv H6. repeat rewrite of_nat_length_LN.
      repeat rewrite <- LN_app. change (LN [Syntax.Plus]) with 1.
      repeat rewrite <- N.add_assoc. rewrite LN_app. apply ExecDone.
      unfold program_of_plist. simpl. replace (_ =? _) with false. reflexivity.
      rewrite <- LN_app. lia.
  - (* Minus *)
    simpl AEVAL. inv H0. replace op with Minus in * by solve_in. inv H1.
      eapply exec_prog_trans. eauto.
      eapply exec_prog_trans. eapply IHa2. apply models_store_cons. eassumption. eassumption.
      econstructor. now rewrite program_of_plist_exact.
      constructor; now rewrite program_of_plist_exact.
      simpl in H6. inv H6. repeat rewrite of_nat_length_LN.
      repeat rewrite <- LN_app. change (LN [Syntax.Minus]) with 1.
      repeat rewrite <- N.add_assoc. rewrite LN_app. apply ExecDone.
      unfold program_of_plist. simpl. replace (_ =? _) with false. reflexivity.
      rewrite <- LN_app. lia.
  - (* Mult *)
    simpl AEVAL. inv H0. replace op with Mult in * by solve_in. inv H1.
      eapply exec_prog_trans. eauto.
      eapply exec_prog_trans. eapply IHa2. apply models_store_cons. eassumption. eassumption.
      econstructor. (* oh my *)
Admitted.