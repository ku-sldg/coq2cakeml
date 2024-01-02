Require Export Loader. (* I'd like this to be Coq2CakeML *)

Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import CakeSem.EvaluateTheory.

Require Import StructTact.StructTactics.
Require Import Lists.List.
Import ListNotations.
Require Import Lia.
Require Import Strings.String.
Open Scope string_scope.

Require Import ExampleInv.

PrintInvariant list.
GenerateInvariant list.
GenerateMatchLemma list.
  intros.
  destruct matched;
    unfold EVAL in *; unfold evaluate in *.
  - intros.
    specialize (H2 st).
    destruct H2 as [v [f [st' [H2 H2']]]].
    clear H4.
    inv H2'.
    simp eval_or_match in H3.
    assert (@nil PARAM0 = []) by reflexivity.
    specialize (H3 H st').
    destruct H3 as [v [f0 [st'0 [H3 H3']]]].
    clear H.
    exists v.
    exists (list_max [f;f0]).
    exists st'0.
    simp eval_or_match; simpl.
    apply (use_maximum_fuel _ [f;f0] _) in H2; simpl in H2.
    rewrite H2. simpl.
    simp eval_or_match; simpl.
    simp pmatch; simpl.
    unfold good_cons_env in H0.
    inv H0.
    destruct H5 as [con_name [ps [ty [H51 [H52 [H53 H54]]]]]].
    inv H51.
    rewrite H53.
    simpl in H54.
    rewrite PeanoNat.Nat.eqb_eq in H54.
    subst.
    simpl.
    apply (use_maximum_fuel _ [f;f0] _) in H3; simpl in H3; unfold list_max in H3.
    split.
    rewrite <- sem_env_id.
    unfold extend_dec_env in H3; simpl in H3.
    rewrite <- sem_env_id in H3.
    apply H3.
    assumption.
    unfold list_max; simpl; lia.
    unfold list_max; simpl; lia.
  - unfold evaluate in *. intros.
    specialize (H2 st).
    destruct H2 as [v [f [st' [H2 H2']]]].
    clear H3.
    inv H2'.
    simp eval_or_match in H4.
    assert (p::matched = p::matched) by reflexivity.
    destruct H3 as [v1 [H31 [H32 H33]]].
    specialize (H4 p matched x v1 H H32 H33 st').
    clear H.
    destruct H4 as [v' [f0 [st'0 [H4 H4']]]].
    exists v'.
    exists (list_max [f;f0]).
    exists st'0.
    simp eval_or_match; simpl.
    apply (use_maximum_fuel _ [f;f0] _) in H2; simpl in H2; try (simpl;lia).
    rewrite H2. simpl.
    simp eval_or_match; simpl.
    unfold good_cons_env in H0.
    inv H0; clear H0.
    simp pmatch; simpl.
    inv H6.
    clear H6 H7.
    destruct H3 as [con_name [ps [ty [H3' [H3_nodup [H3_lookup H3_stamp]]]]]].
    destruct H5 as [con_name' [ps' [ty' [H5' [H5_nodup [H5_lookup H5_stamp]]]]]].
    inv H3'. inv H5'.
    rewrite H5_lookup.
    simpl.
    simpl in H5_stamp.
    rewrite PeanoNat.Nat.eqb_eq in H5_stamp. rewrite H5_stamp; simpl.
    destruct (string_eq_dec pat_str1 pat_str0).
    subst.
    inv H1.
    assert (In pat_str0 [pat_str0]) by (constructor; reflexivity).
    contradiction.
    rewrite <- String.eqb_neq in n.
    rewrite n; simpl.
    rewrite H3_lookup; simpl.
    inv H3_stamp.
    rewrite PeanoNat.Nat.eqb_eq in H0.
    subst. simpl.
    simp pmatch; simpl.
    split.
    unfold nsBind, extend_dec_env in H4; simpl in H4.
    apply more_fuel_same_value with f0.
    lia.
    apply H4.
    assumption.
Qed.

Theorem EVAL_ECon_list_nil :
  forall A A_INV env,
    nsLookup ident_string_beq (Short "Nil") (sec env) = Some (0, TypeStamp "Nil" 0) ->
    EVAL env (ECon (Some (Short "Nil")) []) (list_INV A A_INV []).
Proof.
  intros A AINV env HnsLookup st.
  unfold evaluate.
  do 3 eexists.
  split.
  simp eval_or_match; simpl.
  rewrite HnsLookup; simpl.
  simp eval_or_match.
  unfold build_conv.
  unfold ident_string_beq in HnsLookup.
  rewrite HnsLookup. simpl. reflexivity.
  reflexivity.
  Unshelve.
  constructor.
Qed.

Theorem EVAL_ECon_list_Cons :
  forall A A_INV env a xs e1 e2,
    nsLookup ident_string_beq (Short "Cons") (sec env) = Some (2, TypeStamp "Cons" 0) ->
    EVAL env e1 (A_INV a) ->
    EVAL env e2 (list_INV A A_INV xs) ->
    EVAL env (ECon (Some (Short "Cons")) [e1;e2]) (list_INV A A_INV (a::xs)).
Proof.
  intros A AINV env a xs e1 e2 HnsLookup He1 He2.
  unfold EVAL, evaluate in *.
  intro st.
  specialize He2 with st.
  destruct He2 as [v2  [f2  [st2  [Hevale2 HINVe2]]]].
  specialize He1 with st2.
  destruct He1 as [v1  [f1  [st1  [Hevale1 HINVe1]]]].
  apply (more_fuel_same_value f1 (f1 + f2)) in Hevale1.
  apply (more_fuel_same_value f2 (f1 + f2)) in Hevale2.
  unfold evaluate in *.
  do 3 eexists.
  split.
  simp eval_or_match; simpl.
  rewrite HnsLookup; simpl.
  simp eval_or_match; simpl.
  rewrite Hevale2; simpl.
  rewrite Hevale1; simpl.
  unfold ident_string_beq in HnsLookup.
  rewrite HnsLookup; simpl.
  reflexivity.
  simpl.
  do 2 eexists.
  split.
  reflexivity.
  split; assumption.
  lia.
  lia.
Qed.

Require Import CakeSem.Evaluate.
GenerateCertificate map.
Obligations.
  intros A AINV B BINV.
  apply EVAL_EFun.
  intros f v H.
  apply EVAL_remove_EQ.
  - constructor. constructor.
  - intros x.
    apply EVAL_ELetrec.
    induction x.
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) [].
      + reflexivity.
      + good_cons_env_solve.
      + NoDup_solve.
      + apply EVAL_EVar with u; try reflexivity; try assumption.
      + intro.
        eapply EVAL_ECon_list_nil.
        reflexivity.
      + intros aa ab ac ad contra.
        inv contra.
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) (a::x).
      + reflexivity.
      + good_cons_env_solve.
      + NoDup_solve.
      + eapply EVAL_EVar; try reflexivity; try assumption.
      + intro contra. inv contra.
      + intros.
        eapply EVAL_ECon_list_Cons.
        -- reflexivity.
        -- eapply EVAL_EApp_Opapp.
           ** apply EVAL_EVar with v;try reflexivity; try assumption.
              apply H.
           ** eapply EVAL_EVar ; try reflexivity; try assumption.
        -- eapply EVAL_EApp_Opapp.
           ** eapply EVAL_EVar_Recclosure.
              ++ intros.
                 reflexivity.
              ++ apply IHx.
           ** eapply EVAL_EVar; try reflexivity; try assumption.
              unfold EQ. split; inv H0; try reflexivity; try assumption.
Qed.

FinishProgram "map".
Obligations.
  unfold DECL.
  eexists.
  simpl.
  simp evaluate_decs; simpl.
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  reflexivity.
  Unshelve.
  constructor.
Qed.
