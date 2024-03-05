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
Require Import Tactics.

Require Import Extraction.

PrintInvariant list.
GenerateInvariant list.
GenerateMatchLemma list.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    simpl.
    final_solve.

  - solve_case Hcase0 [match_arg_v; match_arg_v0] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant nat.

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
  simpl.
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
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  reflexivity.
  Unshelve.
  constructor.
Qed.
