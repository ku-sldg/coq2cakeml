Require Import Constants.
From CakeMLExtraction Require Import Loader. (* I'd like this to be Coq2CakeML *)

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

Require Import Tactics.

(* Axiom Test  *)
BeginProgram.
GenerateInvariant nat.

Axiom axio_plus : nat -> nat -> nat.
GenerateCertificate axio_plus. Admitted.
GenerateDeclaration axio_plus. Admitted.

(* All EVAL says is that there exists SOME value that is fulfills the *)
(* refinement invariant, but not what that value is. *)

Axiom axio_poly : forall A : Type, A -> A.
GenerateCertificate axio_poly. Admitted.
GenerateDeclaration axio_poly. Admitted.

(* map examples *)
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

Fixpoint my_map (A B : Type) (f : A -> B) l :=
  match l with
  | [] => []
  | x::xs => (f x)::(my_map A B f xs)
  end.

GenerateCertificate my_map.
Proof.
  intros A A_INV B B_INV.
  apply EVAL_ELetrec_noEQ.
  intros f v f_INV.
  apply EVAL_remove_EQ; try repeat constructor.
  intros la.
  apply EVAL_EFun.
  intro la'.
  generalize dependent f.
  generalize dependent v.
  generalize dependent la'.
  induction la.
  - intros la' v f f_INV v0 v0_INV.
    apply (EVAL_EMat_list _ _ A_INV _ _ _ _ [] (fun x xs => (f x)::(my_map A B f xs)) []).
    * inv v0_INV. reflexivity.
    * good_cons_env_solve.
    * apply EVAL_EVar with v0; try reflexivity; try assumption.
      inv v0_INV.
      assumption.
    * intro.
      apply EVAL_ECon_nil.
      reflexivity.
    * intros a aa b bb contra.
      inv contra.
  - intros la' v f f_INV v0 v0_INV.
    apply (EVAL_EMat_list _ _ A_INV _ _ _ _ [] (fun x xs => (f x)::(my_map A B f xs)) (a::la)).
    * inv v0_INV. reflexivity.
    * good_cons_env_solve.
    * apply EVAL_EVar with v0; try reflexivity; try assumption.
      inv v0_INV. assumption.
    * intro contra. inv contra.
    * intros a' as' v' vs' Heq INV_v' INV_vs'.
      apply EVAL_ECon_cons.
      + reflexivity.
      + eapply EVAL_EApp_Opapp.
        -- apply EVAL_EVar with v; try reflexivity; try assumption.
           apply f_INV.
        -- apply EVAL_EVar with v'; try reflexivity; try assumption.
      + eapply EVAL_EApp_Opapp.
        -- eapply EVAL_EApp_Opapp.
           ++ eapply EVAL_EVar_Recclosure.
              reflexivity.
              intros.
              apply EVAL_EFun.
              intros.
              unfold my_map.
              apply IHla.
              apply H.
              apply H0.
           ++ apply EVAL_EVar with v; try reflexivity; try assumption.
              split. reflexivity.
              apply f_INV.
        -- apply EVAL_EVar with vs'; try reflexivity; try assumption.
           split.
           inv Heq. reflexivity.
           apply INV_vs'.
Qed.

GenerateDeclaration my_map.
Proof.
  unfold DECL.
  exists 0.
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  simp pmatch; simpl.
  reflexivity.
Qed.

(* (* Playin *) *)

Theorem EVAL_EVar_Recclosure2
     : forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop)
         (f : A -> B) (fname name : tvarN) (body : exp) (env cl_env : sem_env val),
       nsLookup ident_string_beq (Short fname) (sev env) =
       Some (Recclosure cl_env [(fname, name, body)] fname) ->
       (forall (n : A) (v : val),
        AINV n v ->
        EVAL
          (bind_variable_name name v
             (update_sev cl_env (build_rec_env [(fname, name, body)] cl_env (sev cl_env)))) body
          (BINV (f n))) -> EVAL env (EVar (Short fname)) (FUNC AINV BINV f).
Proof.
  intros.
  unfold EVAL in *.
  unfold evaluate in *.
  intros.
  eexists.
  eexists.
  eexists.
  split.
  simp eval_or_match; simpl.
  rewrite H. simpl.
  reflexivity.
  unfold FUNC.
  intros x v H1.
  assert (H0' := (H0 x v (H1) st)).
  destruct H0' as [v0 [f0 [st' [Hevalv0 HINVv0]]]].
  eexists.
  split.
  - apply HINVv0.
  - unfold app_returns.
    intros v1 HINVv1 st0.
    assert (H0'' := (H0 x v1 (HINVv1) st0)).
    destruct H0'' as [v0' [f0' [st'' [Hevalv1 HINVv1']]]].
    do 3 eexists.
    eexists.
    split.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
    split.
    unfold eval_rel.
    unfold evaluate.
    eexists.
    apply Hevalv1.
    apply HINVv1'.
    Unshelve. constructor.
Qed.

(*   (* Done Playin *) *)

(* Require Import CakeSem.Evaluate. *)
GenerateCertificate map.
Obligations.
intros A AINV B BINV.
apply EVAL_EFun.
  intros f v H.
  apply EVAL_remove_EQ.
  - constructor. constructor.
  - intros x.
    apply EVAL_ELetrec.
    induction x as [| a x'].
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) [].
      + reflexivity.
      + good_cons_env_solve.
      + apply EVAL_EVar with u; [reflexivity|assumption].
      + intro.
        eapply EVAL_ECon_nil.
        reflexivity.
      + intros aa ab ac ad contra.
        inv contra.
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) (a::x').
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
              ++ apply IHx'.
           ** eapply EVAL_EVar; try reflexivity; try assumption.
              unfold EQ. split; inv H0; try reflexivity; try assumption.
Qed.

Theorem diff_map_defs_EVAL :
  forall (A : Type) (A_INV : A -> val -> Prop) (B : Type) (B_INV : B -> val -> Prop),
    EVAL cake_env5
      (EFun "f"
         (ELetrec
            [("map", "l",
               EMat (EVar (Short "l"))
                 [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
                  (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"],
                    ECon (Some (Short "Cons"))
                      [EApp Opapp [EVar (Short "f"); EVar (Short "a")];
                       EApp Opapp [EVar (Short "map"); EVar (Short "t")]])])]
            (EVar (Short "map"))))
      (FUNC (FUNC A_INV B_INV) (FUNC (list_INV A A_INV) (list_INV B B_INV))
         (my_map A B)).
Proof.
intros A AINV B BINV.
apply EVAL_EFun.
  intros f v H.
  apply EVAL_remove_EQ.
  - constructor. constructor.
  - intros x.
    apply EVAL_ELetrec.
    induction x as [| a x'].
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(map f l)) [].
      + reflexivity.
      + good_cons_env_solve. (* if this fails check the passed in environment argument to the theorem *)
      + apply EVAL_EVar with u; [reflexivity|assumption].
      + intro.
        eapply EVAL_ECon_nil.
        reflexivity.
      + intros aa ab ac ad contra.
        inv contra.
    * intros u H'.
      apply EVAL_EMat_list with A AINV [] (fun a l => (f a)::(my_map A B f l)) (a::x'). (* change here : map ==> my_map A B*)
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
              ++ apply IHx'.
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

(* PrintProgram. *)

FinishProgram "map".
Obligations.
simpl;
  repeat (next; try reflexivity).
apply DECL_indiv_axio_plus_cert_thm.
apply DECL_indiv_axio_poly_cert_thm.
apply DECL_indiv_map_cert_thm.
reflexivity.
Qed.
