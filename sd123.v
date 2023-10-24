Require Import String.
Require Import Lia.


Inductive List (T : Type) :=
  | empty : List T
  | add : (List T) -> T -> (List T).

Fixpoint In (T : Type) (S: (List T)) (e: T) : Prop :=
  match S with
    | (empty _) => False
    | (add _ V a) => a = e \/ (In T V e)
  end.

Inductive expressionSD :=
  | atom : string -> expressionSD
  | notSD : expressionSD -> expressionSD
  | and : expressionSD -> expressionSD -> expressionSD
  | or : expressionSD -> expressionSD -> expressionSD
  | cond : expressionSD -> expressionSD -> expressionSD
  | bicond : expressionSD -> expressionSD -> expressionSD.

Inductive proofSD (premises: (List expressionSD)) (conclusion: expressionSD) : Prop :=
  | repetition : (In expressionSD premises conclusion) -> (proofSD premises conclusion)
  | andIntro : forall (a b: expressionSD),
      (conclusion = (and a b)) -> (proofSD premises a) -> (proofSD premises b)
      -> (proofSD premises conclusion)
  | andElimLeft : forall (b: expressionSD),
      (proofSD premises (and conclusion b))
      -> (proofSD premises conclusion)
  | andElimRight : forall (b: expressionSD),
      (proofSD premises (and b conclusion))
      -> (proofSD premises conclusion)
  | orIntroLeft : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD premises a)
      -> (proofSD premises conclusion)
  | orIntroRight : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD premises b)
      -> (proofSD premises conclusion)
  | orElim : forall (a b: expressionSD),
      (proofSD premises (or a b)) ->
      (proofSD (add expressionSD premises a) conclusion) ->
      (proofSD (add expressionSD premises b) conclusion) ->
      (proofSD premises conclusion)
  | condIntro : forall (a b : expressionSD),
      (conclusion = (cond a b)) ->
      (proofSD (add expressionSD premises a) b) ->
      (proofSD premises conclusion)
  | condElim : forall (a : expressionSD),
      (proofSD premises a) ->
      (proofSD premises (cond a conclusion)) ->
      (proofSD premises conclusion)
  | notSDIntro : forall (a b : expressionSD),
      (conclusion = (notSD a)) ->
      (proofSD (add expressionSD premises a) b) ->
      (proofSD (add expressionSD premises a) (notSD b)) ->
      (proofSD premises conclusion)
  | notSDElim : forall (b : expressionSD),
      (proofSD (add expressionSD premises (notSD conclusion)) b) ->
      (proofSD (add expressionSD premises (notSD conclusion)) (notSD b)) ->
      (proofSD premises conclusion).

Inductive proofSD2 (premises: (List expressionSD)) (conclusion: expressionSD) : Prop :=
  | repetition2 : (In expressionSD premises conclusion) -> (proofSD2 premises conclusion)
  | andIntro2 : forall (a b: expressionSD),
      (conclusion = (and a b)) -> (proofSD2 premises a) -> (proofSD2 premises b)
      -> (proofSD2 premises conclusion)
  | andElimLeft2 : forall (b: expressionSD),
      (proofSD2 premises (and conclusion b))
      -> (proofSD2 premises conclusion)
  | andElimRight2 : forall (b: expressionSD),
      (proofSD2 premises (and b conclusion))
      -> (proofSD2 premises conclusion)
  | orIntroLeft2 : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD2 premises a)
      -> (proofSD2 premises conclusion)
  | orIntroRight2 : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD2 premises b)
      -> (proofSD2 premises conclusion)
  | orElim2 : forall (a b: expressionSD),
      (proofSD2 premises (or a b)) ->
      (proofSD2 (add expressionSD premises a) conclusion) ->
      (proofSD2 (add expressionSD premises b) conclusion) ->
      (proofSD2 premises conclusion)
  | condIntro2 : forall (a b : expressionSD),
      (conclusion = (cond a b)) ->
      (proofSD2 (add expressionSD premises a) b) ->
      (proofSD2 premises conclusion)
  | condElim2 : forall (a : expressionSD),
      (proofSD2 premises a) ->
      (proofSD2 premises (cond a conclusion)) ->
      (proofSD2 premises conclusion)
  | notSDIntro2 : forall (a b : expressionSD),
      (conclusion = (notSD a)) ->
      (proofSD2 (add expressionSD premises a) b) ->
      (proofSD2 (add expressionSD premises a) (notSD b)) ->
      (proofSD2 premises conclusion)
  | explosion2 : forall (b : expressionSD),
      (proofSD2 premises b) ->
      (proofSD2 premises (notSD b)) ->
      (proofSD2 premises conclusion)
  | DNE2 : (proofSD2 premises (notSD (notSD conclusion))) -> (proofSD2 premises conclusion).

Inductive proofSD3 (premises: (List expressionSD)) (conclusion: expressionSD) : Prop :=
  | repetition3 : (In expressionSD premises conclusion) -> (proofSD3 premises conclusion)
  | andIntro3 : forall (a b: expressionSD),
      (conclusion = (and a b)) -> (proofSD3 premises a) -> (proofSD3 premises b)
      -> (proofSD3 premises conclusion)
  | andElimLeft3 : forall (b: expressionSD),
      (proofSD3 premises (and conclusion b))
      -> (proofSD3 premises conclusion)
  | andElimRight3 : forall (b: expressionSD),
      (proofSD3 premises (and b conclusion))
      -> (proofSD3 premises conclusion)
  | orIntroLeft3 : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD3 premises a)
      -> (proofSD3 premises conclusion)
  | orIntroRight3 : forall (a b: expressionSD),
      (conclusion = (or a b)) -> (proofSD3 premises b)
      -> (proofSD3 premises conclusion)
  | orElim3 : forall (a b: expressionSD),
      (proofSD3 premises (or a b)) ->
      (proofSD3 (add expressionSD premises a) conclusion) ->
      (proofSD3 (add expressionSD premises b) conclusion) ->
      (proofSD3 premises conclusion)
  | condIntro3 : forall (a b : expressionSD),
      (conclusion = (cond a b)) ->
      (proofSD3 (add expressionSD premises a) b) ->
      (proofSD3 premises conclusion)
  | condElim3 : forall (a : expressionSD),
      (proofSD3 premises a) ->
      (proofSD3 premises (cond a conclusion)) ->
      (proofSD3 premises conclusion)
  | notSDIntro3 : forall (a b : expressionSD),
      (conclusion = (notSD a)) ->
      (proofSD3 (add expressionSD premises a) b) ->
      (proofSD3 (add expressionSD premises a) (notSD b)) ->
      (proofSD3 premises conclusion)
  | explosion3 : forall (b : expressionSD),
      (proofSD3 premises b) ->
      (proofSD3 premises (notSD b)) ->
      (proofSD3 premises conclusion).

Theorem adding_preserves_expansion : forall (a b : (List expressionSD)) (c : expressionSD),
  (forall (x : expressionSD), (In expressionSD a x) -> (In expressionSD b x)) -> (
    forall (x : expressionSD),
    (In expressionSD (add expressionSD a c) x) ->
    (In expressionSD (add expressionSD b c) x)
  ).
Proof.
  intros.
  simpl. simpl in H0.
  destruct H0. tauto.
  pose proof H x H0.
  tauto.
Qed.

Theorem SD_expandable_premises : forall (premises : (List expressionSD))
    (conclusion : expressionSD),
  (proofSD premises conclusion) ->
  forall (expansion : (List expressionSD)),
  (forall (a : expressionSD), (In expressionSD premises a) -> (In expressionSD expansion a)) ->
      (proofSD expansion conclusion).
Proof.
  intros premises conclusion proofSD.
  induction proofSD; intros.
  (* repetition *)
  apply repetition. pose proof H0 conclusion H. auto.
  (* andIntro *)
  pose proof IHproofSD1 expansion H0. pose proof IHproofSD2 expansion H0.
  apply andIntro with a b; assumption.
  (* andElimLeft *)
  pose proof IHproofSD expansion H.
  apply andElimLeft with b; assumption.
  (* andElimRight *)
  pose proof IHproofSD expansion H.
  apply andElimRight with b; assumption.
  (* orIntroLeft *)
  pose proof IHproofSD expansion H0.
  apply orIntroLeft with a b; assumption.
  (* orIntroRight *)
  pose proof IHproofSD expansion H0.
  apply orIntroRight with a b; assumption.
  (* orElim *)
  pose proof IHproofSD1 expansion H.
  pose proof adding_preserves_expansion premises expansion a H.
  pose proof adding_preserves_expansion premises expansion b H.
  pose proof IHproofSD2 (add expressionSD expansion a) H1.
  pose proof IHproofSD3 (add expressionSD expansion b) H2.
  apply orElim with a b; assumption.
  (* condIntro *)
  pose proof adding_preserves_expansion premises expansion a H0.
  pose proof IHproofSD (add expressionSD expansion a) H1.
  apply condIntro with a b; assumption.
  (* condElim *)
  pose proof IHproofSD1 expansion H.
  pose proof IHproofSD2 expansion H.
  apply condElim with a; assumption.
  (* notSDIntro *)
  pose proof adding_preserves_expansion premises expansion a H0.
  pose proof IHproofSD1 (add expressionSD expansion a) H1.
  pose proof IHproofSD2 (add expressionSD expansion a) H1.
  apply notSDIntro with a b; assumption.
  (* notSDElim *)
  pose proof adding_preserves_expansion premises expansion (notSD conclusion) H.
  pose proof IHproofSD1 (add expressionSD expansion (notSD conclusion)) H0.
  pose proof IHproofSD2 (add expressionSD expansion (notSD conclusion)) H0.
  apply notSDElim with b; assumption.
Qed.

Theorem SD2_expandable_premises : forall (premises : (List expressionSD))
    (conclusion : expressionSD),
  (proofSD2 premises conclusion) ->
  forall (expansion : (List expressionSD)),
  (forall (a : expressionSD), (In expressionSD premises a) -> (In expressionSD expansion a)) ->
      (proofSD2 expansion conclusion).
Proof.
  intros premises conclusion proofSD.
  induction proofSD; intros.
  (* repetition *)
  apply repetition2. pose proof H0 conclusion H. auto.
  (* andIntro *)
  pose proof IHproofSD1 expansion H0. pose proof IHproofSD2 expansion H0.
  apply andIntro2 with a b; assumption.
  (* andElimLeft *)
  pose proof IHproofSD expansion H.
  apply andElimLeft2 with b; assumption.
  (* andElimRight *)
  pose proof IHproofSD expansion H.
  apply andElimRight2 with b; assumption.
  (* orIntroLeft *)
  pose proof IHproofSD expansion H0.
  apply orIntroLeft2 with a b; assumption.
  (* orIntroRight *)
  pose proof IHproofSD expansion H0.
  apply orIntroRight2 with a b; assumption.
  (* orElim *)
  pose proof IHproofSD1 expansion H.
  pose proof adding_preserves_expansion premises expansion a H.
  pose proof adding_preserves_expansion premises expansion b H.
  pose proof IHproofSD2 (add expressionSD expansion a) H1.
  pose proof IHproofSD3 (add expressionSD expansion b) H2.
  apply orElim2 with a b; assumption.
  (* condIntro *)
  pose proof adding_preserves_expansion premises expansion a H0.
  pose proof IHproofSD (add expressionSD expansion a) H1.
  apply condIntro2 with a b; assumption.
  (* condElim *)
  pose proof IHproofSD1 expansion H.
  pose proof IHproofSD2 expansion H.
  apply condElim2 with a; assumption.
  (* notSDIntro *)
  pose proof adding_preserves_expansion premises expansion a H0.
  pose proof IHproofSD1 (add expressionSD expansion a) H1.
  pose proof IHproofSD2 (add expressionSD expansion a) H1.
  apply notSDIntro2 with a b; assumption.
  (* explosion *)
  pose proof IHproofSD1 expansion H.
  pose proof IHproofSD2 expansion H.
  apply explosion2 with b; assumption.
  (* DNE *)
  pose proof IHproofSD expansion H.
  apply DNE2; assumption.
Qed.

Theorem SD2_equals_SD : forall (premises : (List expressionSD)) (conclusion : expressionSD),
  (proofSD2 premises conclusion) <-> (proofSD premises conclusion).
Proof.
  intros premises conclusion. unfold iff. split.
  intros SD2Proof.
  (* === FIRST DIRECTION (SD2 -> SD) === *)
  induction SD2Proof.
  (* repetition *)
  apply repetition. assumption.
  (* andIntro *)
  apply andIntro with a b; assumption.
  (* andElimLeft *)
  apply andElimLeft with b; assumption.
  (* andElimRight *)
  apply andElimRight with b; assumption.
  (* orIntroLeft *)
  apply orIntroLeft with a b; assumption.
  (* orIntroRight *)
  apply orIntroRight with a b; assumption.
  (* orElim *)
  apply orElim with a b; assumption.
  (* condIntro *)
  apply condIntro with a b; assumption.
  (* condElim *)
  apply condElim with a; assumption.
  (* notSDIntro *)
  apply notSDIntro with a b; assumption.
  (* explosion. *)
  (* we construct a proof with negation elimination. *)
  assert (proofSD
    (add expressionSD premises (notSD conclusion))
    b
  ).
  apply SD_expandable_premises with premises.
    assumption. intros. simpl. tauto.
  assert (proofSD
    (add expressionSD premises (notSD conclusion))
    (notSD b)
  ).
  apply SD_expandable_premises with premises.
    assumption. intros. simpl. tauto.
  apply notSDElim with b.    
  assumption.
  assumption.
  (* DNE *)
  (* we again construct a proof with negation elimination. *)
  apply notSDElim with (notSD conclusion).
  apply repetition. simpl. auto.
  apply SD_expandable_premises with premises.
    assumption. intros. simpl. tauto.
  (* === SECOND DIRECTION (SD -> SD2) === *)
  intros SDProof.
  induction SDProof.
  (* repetition *)
  apply repetition2. assumption.
  (* andIntro *)
  apply andIntro2 with a b; assumption.
  (* andElimLeft *)
  apply andElimLeft2 with b; assumption.
  (* andElimRight *)
  apply andElimRight2 with b; assumption.
  (* orIntroLeft *)
  apply orIntroLeft2 with a b; assumption.
  (* orIntroRight *)
  apply orIntroRight2 with a b; assumption.
  (* orElim *)
  apply orElim2 with a b; assumption.
  (* condIntro *)
  apply condIntro2 with a b; assumption.
  (* condElim *)
  apply condElim2 with a; assumption.
  (* notSDIntro *)
  apply notSDIntro2 with a b; assumption.
  (* notSDElim *)
  assert (proofSD2
    premises
    (notSD (notSD conclusion))
  ).
  apply notSDIntro2 with (notSD conclusion) b; tauto.
  apply DNE2.
  assumption.
Qed.

(* We will consider a Heyting algebra model theory built on the
  complements of heads of the naturals. *)
Inductive hypernat :=
  | fin : nat -> hypernat
  | infty.

Definition hmin (a b : hypernat) :=
  match a with
    | infty => b
    | fin x => match b with
      | infty => fin x
      | fin y => fin (min x y)
    end
  end.

Definition hmax (a b : hypernat) :=
  match a with
    | infty => infty
    | fin x => match b with
      | infty => infty
      | fin y => fin (max x y)
    end
  end.

Definition hleq (a b : hypernat) : Prop :=
  match a with
    | infty => b = infty
    | fin x => match b with
        | infty => True
        | fin y => x <= y
    end
  end.

Fixpoint nhimpl (a b : nat) :=
  match a with
    | 0 => b
    | (S x) => match b with
      | 0 => 0
      | (S y) => match (nhimpl x y) with
        | 0 => 0
        | (S z) => (S (S z))
      end
    end
  end.

Definition himpl (a b : hypernat) :=
  match a with
    | infty => fin 0
    | fin x => match b with
      | infty => infty
      | fin y => fin (nhimpl x y)
    end
  end.

Definition hassignment := string -> hypernat.

Fixpoint heval (expression : expressionSD) (assign: hassignment) := match expression with
  | atom x => assign x
  | notSD x => (himpl (heval x assign) infty)
  | and a b => (hmax (heval a assign) (heval b assign))
  | or a b => (hmin (heval a assign) (heval b assign))
  | cond a b => (himpl (heval a assign) (heval b assign))
  | bicond a b => (hmax
    (himpl (heval a assign) (heval b assign))
    (himpl (heval b assign) (heval a assign))
  )
end.

Theorem notInfty : forall (n : nat), ((fin n) = infty) -> False.
Proof.
  intros. discriminate.
Qed.


Fixpoint hmax_many (premises : (List hypernat)) : hypernat := match premises with
  | empty _ => (fin 0)
  | (add _ s a) => (hmax a (hmax_many s))
end.

Fixpoint eval_all (premises : List expressionSD) (assign : hassignment): (List hypernat) := match premises with
  | empty _ => empty hypernat
  | (add _ s a) => (add hypernat (eval_all s assign) (heval a assign))
end.

Theorem hleq_trans : forall (a b c : hypernat), (hleq a b) -> (hleq b c) -> (hleq a c).
Proof.
  intros.
  destruct a; destruct b; destruct c; unfold hleq; try auto.
  unfold hleq in H. unfold hleq in H0. lia.
  unfold hleq in H. unfold hleq in H0. exfalso. apply notInfty with n0. assumption.
  unfold hleq in H. exfalso. apply notInfty with n. assumption.
Qed.

Theorem hleq_max : forall (a b : hypernat), (hleq a (hmax a b)).
Proof.
  intros.
  induction a; induction b; simpl; try lia; try tauto.
Qed.

Theorem hleq_max_rev : forall (a b : hypernat), (hleq a (hmax b a)).
Proof.
  intros.
  induction a; induction b; simpl; try lia; try tauto.
Qed.

Theorem hleq_min : forall (a b : hypernat), hleq (hmin a b) a.
Proof.
  intros.
  induction a; induction b; simpl; try lia; try tauto.
Qed.

Theorem hleq_min_rev : forall (a b : hypernat), hleq (hmin b a) a.
Proof.
  intros.
  induction a; induction b; simpl; try lia; try tauto.
Qed.

Theorem hmax_many_monotone : forall (a : hypernat) (V : (List hypernat)),
  hleq (hmax_many V) (hmax_many (add hypernat V a)).
Proof.
  intros.
  induction V; simpl.
  destruct (hmax a (fin 0)); lia.
  eapply hleq_max_rev.
Qed.

Theorem hmax_many_single : forall (a : hypernat) (V : (List hypernat)),
  hleq a (hmax_many (add hypernat V a)).
Proof.
  intros.
  simpl.
  apply hleq_max.
Qed.

Theorem hmax_universal : forall (a b c : hypernat),
  (hleq a c) -> (hleq b c) -> (hleq (hmax a b) c).
Proof.
  intros.
  induction a; induction b; induction c; simpl; try lia; try tauto.
  unfold hleq in H. unfold hleq in H0.
  lia.
Qed.

Theorem hmin_universal : forall (a b c : hypernat),
  (hleq c a) -> (hleq c b) -> (hleq c (hmin a b)).
Proof.
  intros.
  induction a; induction b; induction c; simpl; try tauto.
  unfold hleq in H. unfold hleq in H0. lia.
  exfalso. unfold hleq in H. apply notInfty with n. assumption.
Qed.


Theorem hleq_max_dual : forall (a b c : hypernat),
  (hleq a (hmax b c)) -> (hleq a b) \/ (hleq a c).
Proof.
  intros.
  induction a; induction b; induction c; simpl; try tauto.
  simpl in H. lia.
  exfalso. simpl in H. discriminate.
Qed.

Theorem himpl_true_trivial : forall (a : hypernat),
  (himpl a (fin 0)) = fin 0.
Proof.
  intros.
  induction a; simpl; try tauto.
  induction n; simpl; try tauto.
Qed.

Theorem himpl_false_trivial: forall (a : hypernat),
  a = infty \/ (himpl a infty) = infty.
Proof.
  intros.
  induction a; try tauto.
Qed.

Theorem nhimpl_true_trivial : forall (a : nat),
  (nhimpl a 0) = 0.
Proof.
  intros.
  induction a; simpl; trivial.
Qed.

Theorem nhimpl_true_monotone : forall (a b : nat),
  (nhimpl a b) = 0 -> (nhimpl (S a) (S b)) = 0.
Proof.
intros.
  simpl. rewrite H. trivial.
Qed.

Theorem nhimpl_trivial_plus : forall (a b : nat),
  (nhimpl (a + b) b) = 0.
Proof.
  intros.
  induction b.
  apply nhimpl_true_trivial.
  assert ((a + S b) = S (a + b)). lia.
  rewrite H. apply nhimpl_true_monotone.
  assumption.
Qed.

Theorem nhimpl_trivial : forall (a b : nat),
  b <= a -> (nhimpl a b) = 0.
Proof.
  intros.
  assert (((a - b) + b) = a). lia.
  rewrite <- H0.
  apply nhimpl_trivial_plus.
Qed.

Theorem himpl_trivial : forall (a b : hypernat),
  (hleq b a) -> (himpl a b) = fin 0.
Proof.
  intros.
  induction a; induction b; simpl; try tauto.
  simpl in H.
  pose proof nhimpl_trivial n n0 H.
  rewrite H0.
  trivial.
  exfalso.
  simpl in H.
  discriminate.
Qed.

Theorem nhimpl_nontrivial_plus : forall (a b: nat),
  (nhimpl a (S (a + b))) = S (a + b).
Proof.
  intros.
  induction a; simpl. trivial.
  rewrite IHa. trivial.
Qed.

Theorem nhimpl_nontrivial : forall (a b: nat),
  (a < b) -> (nhimpl a b) = b.
Proof.
  intros.
  assert (b = S (a + (b - a - 1))). lia.
  rewrite H0.
  apply nhimpl_nontrivial_plus.
Qed.


Theorem himpl_trivial_onlyif : forall (a b : hypernat),
  ((himpl a b) = fin 0) -> (hleq b a).
Proof.
  intros.
  induction a; induction b; simpl; try tauto; try discriminate.
  assert (n0 <= n \/ n0 > n). lia.
  destruct H0. trivial.
  simpl in H.
  assert ((nhimpl n n0) = n0).
  apply nhimpl_nontrivial. lia.
  rewrite H1 in H.
  assert (n0 = S (n0 - 1)).
  lia. rewrite H2 in H. discriminate.
Qed.

Theorem nhimpl_either : forall (a b : nat),
  (nhimpl a b) = 0 \/ (nhimpl a b) = b.
Proof.
  intros.
  assert ((b <= a) \/ (a < b)). lia.
  destruct H. left. apply nhimpl_trivial. trivial.
  right. apply nhimpl_nontrivial. trivial.
Qed.

Theorem himpl_either : forall (a b : hypernat),
  (himpl a b) = fin 0 \/ (himpl a b) = b.
Proof.
  intros.
  induction a.
  induction b.
  simpl.
  pose proof nhimpl_either n n0.
  destruct H; rewrite H; tauto.
  simpl. tauto.
  simpl. tauto.
Qed.

Theorem SD3_sound : forall (premises : (List expressionSD)) (conclusion : expressionSD) (assign: hassignment), 
  (proofSD3 premises conclusion) ->
    (hleq (heval conclusion assign) (hmax_many (eval_all premises assign))).
Proof.
  intros.
  induction H.

  (* Case 1: Repetition *)
  induction premises.
  exfalso. auto.
  unfold In in H.
  destruct H.
  rewrite H.
  unfold hmax_many. simpl.
  eapply hleq_max.
  pose proof (IHpremises H).
  apply hleq_trans with (hmax_many (eval_all premises assign)).
  assumption.
  apply hmax_many_monotone.

  (* Case 2: and intro *)
  rewrite H. simpl.
  apply hmax_universal; assumption.

  (* Case 3: and elim left *)
  apply hleq_trans with (heval (and conclusion b) assign); try assumption.
  simpl.
  apply hleq_max.

  (* Case 4: and elim right *)
  apply hleq_trans with (heval (and b conclusion) assign); try assumption.
  simpl.
  apply hleq_max_rev.

  (* Case 5: or intro left *)
  rewrite H. simpl.
  apply hleq_trans with (heval a assign).
  apply hleq_min.
  assumption.

  (* Case 6: or intro right *)
  rewrite H. simpl.
  apply hleq_trans with (heval b assign).
  apply hleq_min_rev.
  assumption.

  (* Case 6: or elim *)
  simpl in IHproofSD3_1. simpl in IHproofSD3_2. simpl in IHproofSD3_3.
  pose proof (hleq_max_dual _ _ _ IHproofSD3_2).
  pose proof (hleq_max_dual _ _ _ IHproofSD3_3).
  destruct H2; destruct H3; try assumption.
  apply hleq_trans with (hmin (heval a assign) (heval b assign)); try assumption.
  apply hmin_universal; try assumption.
  
  (* Case 7: cond intro *)
  rewrite H. simpl.
  simpl in IHproofSD3.
  destruct (heval a assign); destruct (heval b assign).
  simpl. simpl in IHproofSD3.
  destruct (hmax_many (eval_all premises assign)).
  assert (n0 <= n  \/ n < n0). lia. destruct H1.
  assert ((nhimpl n n0) = 0). apply nhimpl_trivial. trivial.
  rewrite H2. lia.
  assert (n0 <= n1). lia.
  pose proof nhimpl_either n n0.
  destruct H3; rewrite H3; lia.
  trivial.
  simpl. simpl in IHproofSD3. destruct (hmax_many (eval_all premises assign)).
    discriminate. trivial.
  simpl. destruct (hmax_many (eval_all premises assign)); lia.
  simpl. destruct (hmax_many (eval_all premises assign)); lia.

  (* Case 8: cond elim *)
  simpl in IHproofSD3_2.
  pose proof himpl_either (heval a assign) (heval conclusion assign).
  destruct H1.
  pose proof himpl_trivial_onlyif (heval a assign) (heval conclusion assign) H1.
  apply hleq_trans with (heval a assign); assumption.
  rewrite <- H1. assumption.

  (* Case 8: not intro *)
  simpl in IHproofSD3_2. rewrite H. simpl.
  pose proof himpl_either (heval a assign) infty.
  destruct H2; rewrite H2; simpl.
  destruct (hmax_many (eval_all premises assign)); lia.
  pose proof himpl_either (heval b assign) infty.
  destruct H3.
  pose proof himpl_trivial_onlyif (heval b assign) infty H3.
  simpl in H4.
  rewrite H4 in IHproofSD3_1.
  simpl in IHproofSD3_1.
  destruct (heval a assign).
  simpl in IHproofSD3_1.
  destruct (hmax_many (eval_all premises assign)).
  discriminate.
  trivial.
  simpl in H2. discriminate.
  rewrite H3 in IHproofSD3_2.
  simpl in IHproofSD3_2.
  destruct (heval a assign).
  simpl in IHproofSD3_2.
  destruct (hmax_many (eval_all premises assign)).
  discriminate.
  trivial.
  simpl in H2.
  discriminate.

  (* Case 9: explosion *)
  simpl in IHproofSD3_2.
  pose proof himpl_either (heval b assign) infty.
  destruct H1.
  destruct (heval b assign).
  simpl in H1. discriminate.
  simpl in IHproofSD3_1. rewrite IHproofSD3_1.
  destruct (heval conclusion assign); simpl; trivial.
  destruct (heval b assign).
  simpl in IHproofSD3_2.
  rewrite IHproofSD3_2.
  destruct (heval conclusion assign); simpl; trivial.
  simpl in IHproofSD3_1.
  rewrite IHproofSD3_1.
  destruct (heval conclusion assign); simpl; trivial.
Qed.


Theorem SD3_not_SD2 : exists (premises : (List expressionSD)) (conclusion : expressionSD),
  (proofSD2 premises conclusion) /\ ~(proofSD3 premises conclusion).
Proof.
  exists (empty expressionSD).
  exists (or (atom "p") (notSD (atom "p"))).
  split.
  assert (proofSD (empty expressionSD) (or (atom "p") (notSD (atom "p")))).
  apply notSDElim with (or (atom "p") (notSD (atom "p"))).
  apply orIntroRight with (atom "p") (notSD (atom "p")); try tauto.
  apply notSDIntro with (atom "p") (or (atom "p") (notSD (atom "p"))); try tauto.
  apply orIntroLeft with (atom "p") (notSD (atom "p")); try tauto.
  apply repetition. unfold In. tauto.
  apply repetition. unfold In. tauto.
  apply repetition. unfold In. tauto.
  apply SD2_equals_SD. assumption.
  unfold not. intros.
  remember (fun (y : string) => fin 1) as x.
  pose proof SD3_sound (empty expressionSD) (or (atom "p") (notSD (atom "p"))) x H.
  simpl in H0.
  rewrite Heqx in H0.
  simpl in H0.
  lia.
Qed.

