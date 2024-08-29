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

GenerateConstLemma nil.
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

GenerateConstLemma cons.
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

Require Import CakeSem.Evaluate.
GenerateCertificate map.
Obligations.
(* (* messing around *) *)
(*   intros A AINV B BINV. *)
(*   apply EVAL_EFun. *)
(*   intros f v H. *)
(*   Search "ELetrec". *)
(*   apply EVAL_ELetrec_noEQ. *)
(*   intros n. *)
(*   induction n. *)
(*     * intros u H'. *)
(*       apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) []. *)
(*       + reflexivity. *)
(*       + good_cons_env_solve. *)
(*       + apply EVAL_EVar with u; try reflexivity; try assumption. *)
(*       + intro. *)
(*         eapply EVAL_ECon_nil. *)
(*         reflexivity. *)
(*       + intros aa ab ac ad contra. *)
(*         inv contra. *)
(*     * intros u H'. *)
(*       apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) (a::n). *)
(*       + reflexivity. *)
(*       + good_cons_env_solve. *)
(*       + eapply EVAL_EVar; try reflexivity; try assumption. *)
(*       + intro contra. inv contra. *)
(*       + intros. *)
(*         eapply EVAL_ECon_cons. *)
(*         -- reflexivity. *)
(*         -- eapply EVAL_EApp_Opapp. *)
(*            ** apply EVAL_EVar with v;try reflexivity; try assumption. *)
(*               apply H. *)
(*            ** eapply EVAL_EVar ; try reflexivity; try assumption. *)
(*         -- eapply EVAL_EApp_Opapp. *)
(*            ** *)
(*               eapply EVAL_EVar_Recclosure. *)
(*               ++ intros. *)
(*                  reflexivity. *)
(*               ++ apply IHn. *)
(*            ** eapply EVAL_EVar; try reflexivity; try assumption. *)
(*               unfold EQ. split; inv H0; try reflexivity; try assumption. *)

(*       (* end messing *) *)
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
        eapply EVAL_ECon_nil.
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
        eapply EVAL_ECon_cons.
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

GenerateDeclaration map.
Proof.
  unfold DECL.
  exists 0.
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  simp pmatch; simpl.
  reflexivity.
Qed.

Theorem DECL_cons' : forall (st : state ST) (env : sem_env val) (d : dec) (ds : list dec)
                       (st' st'' : state ST) (env' env'' env''' : sem_env val),
    DECL st env [d] st' env' ->
    DECL st' (extend_dec_env env' env) ds st'' env'' ->
    env''' = (extend_dec_env env'' env') ->
    DECL st env (d :: ds) st'' env'''.
Proof.
  intros.

  subst.
  eapply DECL_cons.
  apply H.
  apply H0.
Qed.

Theorem DECL_Dlet_Dletrec :
  forall (st st' : state nat) (env env' : sem_env val) locs (funname var : tvarN) (e : exp),
    DECL st env [Dlet locs (Pvar funname) (ELetrec [(funname, var, e)] (EVar (Short funname)))] st' env'
    <->
      DECL st env [Dletrec locs [(funname, var, e)]] st' env'.
Proof.
  intros.
  unfold DECL.
  split; intros; destruct H as [f H]; exists f.
  rewrite <- singular_rec_fun_equiv_DLet_DLetrec; assumption.
  rewrite singular_rec_fun_equiv_DLet_DLetrec; assumption.
Qed.
Theorem DECL_Dtabbrev : forall (st : state ST) (env : sem_env val) l tvs tn ast,
    DECL st env [Dtabbrev l tvs tn ast] st empty_sem_env.
Proof.
  intros.
  unfold DECL.
  exists 0.
  simp evaluate_decs. simpl.
  reflexivity.
Qed.

Ltac next :=
  match goal with
  | |- DECL ?st ?env [Dtype ?l ?td] ?st' ?env' => apply DECL_Dtype; try NoDup_solve
  | |- DECL ?st ?env [Dtabbrev ?l ?tvs ?tn ?ast] ?st' ?env' => apply DECL_Dtabbrev
  | |- DECL ?st ?env [Dlet ?l (Pvar ?n) (ELetrec [(?n,?v,?b)] (EVar (Short ?n)) ) ] ?st' ?env' =>
      rewrite DECL_Dlet_Dletrec;
      eapply DECL_Dletrec
  | |- DECL ?st ?env [?d] ?st' ?env' => fail 1
  | |- DECL ?st ?env (?d::?ds) ?st' ?env' => eapply DECL_cons'
  end;
  unfold state_update_next_type_stamp;
  unfold extend_dec_env;
  simpl.

FinishProgram "map".
Obligations.
simpl.
next.
next.
next.
next.
apply DECL_indiv_map_cert_thm.
reflexivity.
reflexivity.
Qed.
