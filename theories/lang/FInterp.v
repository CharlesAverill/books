Require Import BSyntax Semantics BRelations Tactics.

Fixpoint faeval (s : store) (a : Aexpr) : option N :=
  match a with
  | ConstNat n => Some n
  | VarNat i =>
      match s i with
      | Some (Nat a) => Some a
      | _ => None
      end
  | Plus a1 a2 => 
      match faeval s a1, faeval s a2 with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | Minus a1 a2 => 
      match faeval s a1, faeval s a2 with
      | Some n1, Some n2 => Some (n1 - n2)
      | _, _ => None
      end
  | Mult a1 a2 => 
      match faeval s a1, faeval s a2 with
      | Some n1, Some n2 => Some (n1 * n2)
      | _, _ => None
      end
  | Div a1 a2 => 
      match faeval s a1, faeval s a2 with
      | Some n1, Some n2 => Some (n1 / n2)
      | _, _ => None
      end
  end.

Fixpoint fbeval (s : store) (b : Bexpr) : option bool :=
  match b with
  | ConstBool b => Some b
  | VarBool i =>
      match s i with
      | Some (Bool b) => Some b
      | _ => None
      end
  | Neg b =>
      match fbeval s b with
      | Some b' => Some (negb b')
      | _ => None
      end
  | Or b1 b2 =>
      match fbeval s b1, fbeval s b2 with
      | Some b1', Some b2' => Some (b1' || b2')
      | _, _ => None
      end
  | And b1 b2 =>
      match fbeval s b1, fbeval s b2 with
      | Some b1', Some b2' => Some (b1' && b2')
      | _, _ => None
      end
  end.

Fixpoint fstep (s : store) (st : stmt) : option (store * stmt) :=
  match st with
  | Seq Skip c => Some (s, c)
  | Seq c1 c2 =>
      match fstep s c1 with
      | Some (s', st') => Some (s', Seq st' c2)
      | _ => None
      end
  | Assign v e =>
      match e with
      | AE a =>
          match faeval s a with
          | Some n => Some (update s v (Some (Nat n)), Skip)
          | _ => None
          end
      | BE b =>
          match fbeval s b with
          | Some n => Some (update s v (Some (Bool n)), Skip)
          | _ => None
          end
      end
  | IfThenElse b c1 c2 =>
      match fbeval s b with
      | Some true => Some (s, c1)
      | Some false => Some (s, c2)
      | _ => None
      end
  | While b c => Some (s, IfThenElse b (Seq c (While b c)) Skip)
  | _ => None
  end.

Section FInterpCorrectness.

Lemma faeval_sound :
  forall s a v,
    faeval s a = Some v ->
    aeval s a v.
Proof.
  induction a; intros; simpl in H; inv H.
  - constructor.
  - constructor. destruct (s i); inv H1. destruct s0; now inv H0.
  - destruct (faeval s a1) eqn:E0, (faeval s a2) eqn:E1; try discriminate.
    inv H1. econstructor; eauto. exact I.
  - destruct (faeval s a1) eqn:E0, (faeval s a2) eqn:E1; try discriminate.
    inv H1. econstructor; eauto. exact I.
  - destruct (faeval s a1) eqn:E0, (faeval s a2) eqn:E1; try discriminate.
    inv H1. econstructor; eauto. exact I.
  - destruct (faeval s a1) eqn:E0, (faeval s a2) eqn:E1; try discriminate.
    inv H1. econstructor; eauto. exact I.
Qed.

Lemma fbeval_sound :
  forall s b v,
    fbeval s b = Some v ->
    beval s b v.
Proof.
  induction b; intros; simpl in H; inv H.
  - constructor.
  - constructor. destruct (s i); inv H1. destruct s0; now inv H0.
  - destruct (fbeval s b) eqn:E; try discriminate. inv H1. econstructor; eauto. exact I.
  - destruct (fbeval s b1) eqn:E0, (fbeval s b2) eqn:E1; try discriminate.
    inv H1. eapply EBBop; eauto. exact I.
  - destruct (fbeval s b1) eqn:E0, (fbeval s b2) eqn:E1; try discriminate.
    inv H1. eapply EBBop; eauto. exact I.
Qed.

Theorem fstep_sound :
  forall s1 st1 s2 st2,
    fstep s1 st1 = Some (s2, st2) ->
    step s1 st1 s2 st2.
Proof with auto.
  induction st1; intros.
  - (* Skip *)
      inversion H.
  - (* Seq *)
      simpl in H.
      destruct st1_1. inv H.
        constructor.
        all: destruct (fstep s1 _); try discriminate; destruct p; inv H; auto.
  - (* Assign *)
      simpl in H. destruct e.
      -- (* AE *)
          destruct (faeval s1 a) eqn:E; inv H. apply faeval_sound in E.
            constructor. constructor. assumption.
      -- (* BE *)
          destruct (fbeval s1 b) eqn:E; inv H. apply fbeval_sound in E.
            constructor. constructor. assumption.
  - (* IfThenElse *)
      simpl in H. destruct (fbeval s1 b) eqn:E; inv H.
      destruct b0; inv H1.
        constructor. now apply fbeval_sound.
        constructor. now apply fbeval_sound.
  - (* While *)
      simpl in H. inv H. constructor.
Qed.

Lemma faeval_complete :
  forall s a v,
    aeval s a v ->
    faeval s a = Some v.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. now rewrite H.
  - inv H; simpl in *; [now rewrite IHaeval1, IHaeval2|].
    inv H3; simpl in *; [now rewrite IHaeval1, IHaeval2|].
    inv H; simpl in *; [now rewrite IHaeval1, IHaeval2|].
    inv H3; simpl in *; [now rewrite IHaeval1, IHaeval2|]. inv H.
Qed.

Lemma fbeval_complete :
  forall s b v,
    beval s b v ->
    fbeval s b = Some v.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. now rewrite H.
  - inv H. simpl in *. now rewrite IHbeval.
    inv H2.
  - inv H; simpl in *; [now rewrite IHbeval1, IHbeval2|].
    inv H3; simpl in *; [now rewrite IHbeval1, IHbeval2|].
    inv H.
Qed.

Lemma fstep_complete :
  forall s1 st1 s2 st2,
    step s1 st1 s2 st2 ->
    fstep s1 st1 = Some (s2, st2).
Proof.
  intros. induction H.
  - (* Seq *)
    simpl. rewrite IHstep. destruct c1; inv IHstep; auto.
  - (* Seq Skip c *) reflexivity.
  - (* Assign *)
    destruct e; simpl.
    -- inv H. apply faeval_complete in H2. now rewrite H2.
    -- inv H. apply fbeval_complete in H2. now rewrite H2.
  - (* IfThenElse true *)
    simpl. apply fbeval_complete in H. now rewrite H.
  - (* IfThenElse false *)
    simpl. apply fbeval_complete in H. now rewrite H.
  - (* While *) reflexivity.
Qed.
