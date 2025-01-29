(* (** ManifestGenerator Translation *) *)

(** Things to fix *)
(* Const in refinement invariant generator *)
(* Handle ConstRefs in the certificate generator *)
(* Move refinement invariant generation out of certificate generator *)

(** Future work *)
(* TypeClasses *)
(* Axioms *)

(** Types *)
(* PolicyT = list (prod A B) *)
(* ID_Type -> Axiom *)
(* Plc, ASP_ID, Term, EnvironmentM *)
(* Manifest *)
(* MapC *)
(* EnvironmentM *)

(** Functions *)
(* manifest_generator' *)


(* Current kludge to handle 8.20 changes for now *)
Require Import Strings.String.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Namespace.
Require Import CakeMLExtraction.RefineInv.
Require Import CakeMLExtraction.EvaluateDecsWrapper.
(* *)
Require Import CakeMLExtraction.Loader.
Require Import CakeMLExtraction.Tactics.
Require Import Manifest_Generator.
Require Import Manifest.
Require Import Manifest_Admits.
Require Import Term_Defs_Core.
Require Import Maps.
Require Import AbstractedTypes.
Require Import Params_Admits.

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Lia.

Require Import CakeSem.Evaluate.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import StructTact.StructTactics.

(* Close Scope cop_ent_scope. *)
(* Unset Printing Matching. *)
(* Unset Printing Factorizable Match Patterns. *)

Require Import CakeMLExtraction.EnvWrangling.

(* DECL Stuff to be moved into Coq2CakeML proper *)
(* Theorem DECL_cons' : forall (st : state ST) (env : sem_env val) (d : dec) (ds : list dec) *)
(*                        (st' st'' : state ST) (env' env'' env''' : sem_env val), *)
(*     DECL st env [d] st' env' -> *)
(*     DECL st' (merge_envs env' env) ds st'' env'' -> *)
(*     env''' = (merge_envs env'' env') -> *)
(*     DECL st env (d :: ds) st'' env'''. *)
(* Proof. *)
(*   intros. *)
(*   subst. *)
(*   eapply DECL_cons. *)
(*   apply H. *)
(*   apply H0. *)
(* Qed. *)

(* Theorem DECL_Lemma : forall (st : state ST) (env env' : sem_env val) (locs : locs) (name : tvarN) (e : exp) st' v, *)
(*    eval_rel st env e st' v /\ env' = {| sev := alist_to_ns [(name, v)]; sec := nsEmpty |} -> *)
(*    DECL st env [Dlet locs (Pvar name) e] st' env'. *)
(* Proof. *)
(*   intros. *)
(*   unfold DECL. *)
(*   destruct H. *)
(*   destruct H. *)
(*   exists x. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold evaluate in *. *)
(*   rewrite H. *)
(*   simp pmatch. *)
(*   rewrite H0. *)
(*   reflexivity. *)
(* Qed. *)

(* Definition one_con_check envc e := *)
(*   match e with *)
(*   | ECon cn es => do_con_check envc cn (List.length es) = true *)
(*   | _ => True *)
(*   end. *)

(* Check DECL. *)
Theorem DECL_Dlet_hol_ver :
forall env s1 v e s2 env2 locs,
      DECL s1 env [Dlet locs (Pvar v) e] s2 env2 <->
      exists x, eval_rel s1 env e s2 x /\ (env2 = EnvWrangling.write_v v x empty_sem_env).
Proof.
  intros.
  split.
  - intros.
    unfold DECL in *.
    destruct H.
    simp evaluate_decs in *; simpl in *.
    break_match.
    break_match.
    simp pmatch in *; simpl in *.
    inv H.
    specialize (eval_or_match_sing _ _ _ _ _ _ Heqp).
    intros.
    destruct H0.
    rewrite H0 in Heqp.
    eexists.
    split.
    unfold eval_rel.
    exists x.
    unfold evaluate.
    apply Heqp.
    rewrite H0.
    reflexivity.
    inv H.
  - intros.
    destruct H. destruct H.
    unfold eval_rel in H.
    destruct H.
    unfold DECL.
    exists x0.
    simp evaluate_decs; simpl.
    unfold evaluate in H.
    rewrite H.
    simp pmatch; simpl.
    rewrite H0.
    reflexivity.
Qed.

(* Theorem EVAL_eval_rel : forall AINV env e st, *)
(*   EVAL env e AINV -> *)
(*   exists st' f v, eval_rel st env e st' v /\ st' = fst (evaluate [e] f st env). *)
(* Proof. *)
(*   intros. *)
(*   specialize (H st). *)
(*   destruct H as [v [f [st' [Heval _]]]]. *)
(*   exists st', f, v. *)
(*   unfold eval_rel. *)
(*   split. *)
(*   exists f. *)
(*   assumption. *)
(*   rewrite Heval. *)
(*   reflexivity. *)
(* Qed. *)

(* Theorem DECL_Dtabbrev : forall (st : state ST) (env : sem_env val) l tvs tn ast, *)
(*     DECL st env [Dtabbrev l tvs tn ast] st empty_sem_env. *)
(* Proof. *)
(*   intros. *)
(*   unfold DECL. *)
(*   exists 0. *)
(*   simp evaluate_decs. simpl. *)
(*   reflexivity. *)
(* Qed. *)

(* Theorem DECL_Dlet_Dletrec : *)
(*   forall (st st' : state nat) (env env' : sem_env val) locs (funname var : tvarN) (e : exp), *)
(*     DECL st env [Dlet locs (Pvar funname) (ELetrec [(funname, var, e)] (EVar (Short funname)))] st' env' *)
(*     <-> *)
(*     DECL st env [Dletrec locs [(funname, var, e)]] st' env'. *)
(* Proof. *)
(*   intros. *)
(*   unfold DECL. *)
(*   split; intros; destruct H as [f H]; exists f. *)
(*   rewrite <- singular_rec_fun_equiv_DLet_DLetrec; assumption. *)
(*   rewrite singular_rec_fun_equiv_DLet_DLetrec; assumption. *)
(* Qed. *)

Ltac next_decl :=
  match goal with
  | |- DECL ?st ?env [Dtype ?l ?td] ?st' ?env' => apply DECL_Dtype; try NoDup_solve
  | |- DECL ?st ?env [Dtabbrev ?l ?tvs ?tn ?ast] ?st' ?env' => apply DECL_Dtabbrev
  | |- DECL ?st ?env [Dlet ?l (Pvar ?n) (ELetrec [(?n,?v,?b)] (EVar (Short ?n)) ) ] ?st' ?env' =>
      rewrite DECL_Dlet_Dletrec;
      eapply DECL_Dletrec
  | |- DECL ?st ?env [Dlet ?l ?n ?e ] ?st' ?env' => auto
  | |- DECL ?st ?env [?d] ?st' ?env' => fail 1
  | |- DECL ?st ?env (?d::?ds) ?st' ?env' => eapply DECL_cons'
  end;
  unfold state_update_next_type_stamp;
  unfold extend_dec_env;
  simpl.

(* Theorem idk_yet : forall st env INV name e locs, *)
(*   EVAL env e INV -> *)
(*   exists st' v, DECL st env [Dlet locs (Pvar name) e] st' (EnvWrangling.write_v name v empty_sem_env). *)
(* Proof. *)
(*   intros. *)
(*   specialize (H st). *)
(*   destruct H as [v [f [st' [H _]]]]. *)
(*   unfold DECL. *)
(*   exists st', v, f. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold evaluate in H. *)
(*   rewrite H. *)
(*   simp pmatch; simpl. *)
(*   reflexivity. *)
(* Qed. *)
(* END: DECL Stuff to be moved into Coq2CakeML proper *)

(* Ltac reduce_env := *)
(*   match goal with *)
(*   | [H : EVAL ?env _ _ |- _ ] => *)
(*       remember env as current_env *)
(*   | |- context [EVAL ?env _ _] => *)
(*       remember env as current_env *)
(*   end; *)
(*   match goal with *)
(*   | [H : ?current_env = {| sev := _; sec := _ |} |- _] => *)
(*       clear H *)
(*   end. *)

Ltac normalize_env :=
  unfold bind_variable_name; unfold build_rec_env;
  unfold update_sev; unfold update_sec; unfold nsBind; simpl.

Ltac thing := rewrite DECL_Dlet_hol_ver;
              eexists;
              unfold eval_rel;
              split; [ eexists; unfold evaluate; simp eval_or_match; simpl; try reflexivity | try reflexivity ].

(* Ltac thing :=  unfold DECL; *)
(*                eexists; *)
(*                repeat (simp evaluate_decs; simpl); *)
(*                repeat (simp eval_or_match; simpl); *)
(*                repeat (simp pmatch; simpl); *)
(*                reflexivity. *)

(* Extraction Begins HERE *)
ENV_INIT. (* Hack *)
GenerateInvariant nat.
GenerateDeclaration nat.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_nat_cert_thm : core.

Definition EVAL_ECon_O := fun stmp env =>
                            EVAL_ECon (nat_INV O) [] [] stmp (Short "O") env.
Definition EVAL_ECon_S := fun n e1 stmp env =>
                            EVAL_ECon (nat_INV (S n)) [e1] [(nat_INV n, e1)] stmp (Short "O") env.
GenerateMatchLemma nat.
Proof.
  my_intros.
  handle_matched.
  handle_good_cons.
  destruct matched; subst; normalize_evaluate.
  - destruct_inv Hinv_match.
    solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - destruct_inv Hinv_match.
    solve_case Hcase0 [match_arg_v] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant list.
GenerateDeclaration list.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_list_cert_thm : core.
Definition EVAL_ECon_nil := fun (A : Type) (AINV : A -> val -> Prop) (stmp : stamp) (env : sem_env val) =>
                              EVAL_ECon (list_INV A AINV []) [] [] stmp (Short "Nil") env.
Definition EVAL_ECon_cons := fun (A : Type) (AINV : A -> val -> Prop) (a : A) (l : list A) e1 e2 (stmp : stamp) (env : sem_env val) =>
                               EVAL_ECon (list_INV A AINV (a::l)) [e1;e2] [(AINV a,e1);(list_INV A AINV l,e2)] stmp (Short "Cons") env.
GenerateMatchLemma list.
Proof.
  my_intros.
  handle_matched.
  handle_good_cons.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase0 [match_arg_v; match_arg_v0] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant prod.
GenerateDeclaration prod.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_prod_cert_thm : core.
GenerateMatchLemma prod.
Definition EVAL_ECon_pair := fun (A B : Type) (AINV : A -> val -> Prop) BINV a b e1 e2 (stmp : stamp) (env : sem_env val) =>
                               EVAL_ECon (prod_INV A B AINV BINV (a,b)) [e1;e2] [(AINV a,e1);(BINV b,e2)] stmp (Short "Pair") env.
Proof.
  my_intros.
  handle_matched.
  destruct matched.
  destruct_inv Hinv_match.
  solve_case Hcase [match_arg_v; match_arg_v0] matched_st.
  repeat normalize_fuels [matched_f; case_f].
  repeat handle_good_cons.
  final_solve.
Qed.

GenerateInvariant ID_Type.
GenerateDeclaration ID_Type.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_ID_Type_cert_thm : core.

GenerateInvariant ASP_ID.
GenerateDeclaration ASP_ID.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_ASP_ID_cert_thm : core.

GenerateInvariant Plc.
GenerateDeclaration Plc.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_Plc_cert_thm : core.

GenerateInvariant PolicyT.
GenerateDeclaration PolicyT.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_PolicyT_cert_thm : core.


(* Problem : list and list A need to be treated equivalently *)
(* Solution : eta-conversion (bad? probably) *)
(* note from Future TJ: very bad and super uncool of Past TJ *)

GenerateInvariant manifest_set.
GenerateDeclaration manifest_set.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_manifest_set_cert_thm : core.

(* Problem : Records are non-recursive types (Variants) *)
(* Solution: Check at refinement invariant build time and just don't use a fix *)
(*           expression by changing offset (I am a stable genius) *)
GenerateInvariant Manifest.
GenerateDeclaration Manifest.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_Manifest_cert_thm : core.
Definition EVAL_ECon_Build_Manifest := fun plc asps appraisal_asps uuidPlcs pubKeyPlcs targetPlcs policy
                                   (e1 e2 e3 e4 e5 e6 e7 : exp) (stmp : stamp) (env : sem_env val) =>
   EVAL_ECon (Manifest_INV (Build_Manifest plc asps appraisal_asps uuidPlcs pubKeyPlcs targetPlcs policy))
     [e1;e2;e3;e4;e5;e6;e7]
     [(Plc_INV plc, e1); (manifest_set_INV ASP_ID ASP_ID_INV asps,e2);
      (manifest_set_INV (prod Plc ASP_ID) (prod_INV Plc ASP_ID Plc_INV ASP_ID_INV) appraisal_asps, e3);
      (manifest_set_INV Plc Plc_INV uuidPlcs, e4);
      (manifest_set_INV Plc Plc_INV pubKeyPlcs, e5);
      (manifest_set_INV Plc Plc_INV targetPlcs, e6);
      (PolicyT_INV policy, e7)]
     stmp (Short "Build_Manifest") env.
GenerateMatchLemma Manifest.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  solve_case Hcase [match_arg_v; match_arg_v0; match_arg_v1;
                    match_arg_v2; match_arg_v3; match_arg_v4; match_arg_v5] matched_st.
  repeat normalize_fuels [matched_f; case_f].
  repeat handle_good_cons.
  final_solve.
Qed.

GenerateInvariant MapC.
GenerateDeclaration MapC.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_MapC_cert_thm : core.

GenerateInvariant EnvironmentM.
GenerateDeclaration EnvironmentM.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_EnvironmentM_cert_thm : core.

GenerateInvariant SP.
GenerateDeclaration SP.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_SP_cert_thm : core.
Definition EVAL_ECon_ALL := fun (stmp : stamp) (env : sem_env val) =>
                              EVAL_ECon (SP_INV ALL) [] [] stmp (Short "ALL") env.
Definition EVAL_ECon_NONE := fun (stmp : stamp) (env : sem_env val) =>
                               EVAL_ECon (SP_INV NONE) [] [] stmp (Short "NONE") env.
GenerateMatchLemma SP.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase0 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant Split.
GenerateDeclaration Split.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_Split_cert_thm : core.

GenerateInvariant TARG_ID.
GenerateDeclaration TARG_ID.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_TARG_ID_cert_thm : core.

GenerateInvariant Arg.
GenerateDeclaration Arg.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_Arg_cert_thm : core.

GenerateInvariant ASP_PARAMS.
GenerateDeclaration ASP_PARAMS.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_ASP_PARAMS_cert_thm : core.
Definition EVAL_ECon_asp_paramsC := fun aid larg p targ e1 e2 e3 e4 stmp env =>
                                      EVAL_ECon (ASP_PARAMS_INV (asp_paramsC aid larg p targ))
                                        [e1; e2; e3; e4]
                                        [(ASP_ID_INV aid, e1); (list_INV Arg Arg_INV larg, e2); (Plc_INV p, e3); (TARG_ID_INV targ, e4)]
                                        stmp (Short "Asp_paramsC") env.
GenerateMatchLemma ASP_PARAMS.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  solve_case Hcase [match_arg_v; match_arg_v0; match_arg_v1; match_arg_v2] matched_st.
  repeat normalize_fuels [matched_f; case_f].
  repeat handle_good_cons.
  final_solve.
Qed.

GenerateInvariant FWD.
GenerateDeclaration FWD.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_FWD_cert_thm : core.
Definition EVAL_ECon_COMP := fun stmp env =>
    EVAL_ECon (FWD_INV COMP) [] [] stmp (Short "COMP") env.
Definition EVAL_ECon_ENCR := fun stmp env =>
    EVAL_ECon (FWD_INV ENCR) [] [] stmp (Short "ENCR") env.
Definition EVAL_ECon_EXTD := fun stmp env =>
    EVAL_ECon (FWD_INV EXTD) [] [] stmp (Short "EXTD") env.
Definition EVAL_ECon_KILL := fun stmp env =>
    EVAL_ECon (FWD_INV KILL) [] [] stmp (Short "KILL") env.
Definition EVAL_ECon_KEEP := fun stmp env =>
    EVAL_ECon (FWD_INV KEEP) [] [] stmp (Short "KEEP") env.
GenerateMatchLemma FWD.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase0 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase1 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase2 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase3 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant ASP.
GenerateDeclaration ASP.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_ASP_cert_thm : core.
Definition EVAL_ECon_NULL := fun stmp env =>
    EVAL_ECon (ASP_INV NULL) [] [] stmp (Short "NULL") env.
Definition EVAL_ECon_CPY := fun stmp env =>
    EVAL_ECon (ASP_INV CPY) [] [] stmp (Short "CPY") env.
Definition EVAL_ECon_ASPC := fun sp fwd params e1 e2 e3 stmp env =>
    EVAL_ECon (ASP_INV (ASPC sp fwd params)) [e1; e2; e3]
      [(SP_INV sp, e1); (FWD_INV fwd, e2); (ASP_PARAMS_INV params, e3)] stmp (Short "ASPC") env.
Definition EVAL_ECon_SIG := fun stmp env =>
    EVAL_ECon (ASP_INV SIG) [] [] stmp (Short "SIG") env.
Definition EVAL_ECon_HSH := fun stmp env =>
    EVAL_ECon (ASP_INV HSH) [] [] stmp (Short "HSH") env.
Definition EVAL_ECon_ := fun p e1 stmp env =>
    EVAL_ECon (ASP_INV (ENC p)) [e1] [(Plc_INV p, e1)] stmp (Short "ENC") env.
GenerateMatchLemma ASP.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase0 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase1 [match_arg_v; match_arg_v0; match_arg_v1] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase2 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase3 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
  - solve_case Hcase4 [match_arg_v] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant Term.
GenerateDeclaration Term.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_Term_cert_thm : core.
Definition EVAL_ECon_asp := fun a e1 (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (Term_INV (asp a)) [e1] [(ASP_INV a, e1)] stmp (Short "Asp") env.
Definition EVAL_ECon_att := fun p t e1 e2 (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (Term_INV (att p t)) [e1; e2] [(Plc_INV p, e1); (Term_INV t, e2)] stmp (Short "Att") env.
Definition EVAL_ECon_lseq := fun t1 t2 e1 e2 (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (Term_INV (lseq t1 t2)) [e1; e2]
      [(Term_INV t1, e1); (Term_INV t2, e2)] stmp (Short "Lseq") env.
Definition EVAL_ECon_bseq := fun s t1 t2 e1 e2 e3 (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (Term_INV (bseq s t1 t2)) [e1; e2; e3]
      [(Split_INV s, e1); (Term_INV t1, e2); (Term_INV t2, e3)] stmp (Short "Bseq") env.
Definition EVAL_ECon_bpar := fun s t1 t2 e1 e2 e3 (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (Term_INV (bpar s t1 t2)) [e1; e2; e3]
      [(Split_INV s, e1); (Term_INV t1, e2); (Term_INV t2, e3)] stmp (Short "Bpar") env.
GenerateMatchLemma Term.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase [match_arg_v] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase0 [match_arg_v; match_arg_v0] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase1 [match_arg_v; match_arg_v0] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase2 [match_arg_v; match_arg_v0; match_arg_v1] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase3 [match_arg_v; match_arg_v0; match_arg_v1] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant option.
GenerateDeclaration option.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_option_cert_thm : core.
Definition EVAL_ECon_Some :=
  fun (A : Type) (AINV : A -> val -> Prop) (a : A) (e : exp) (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (option_INV A AINV (Some a)) [e] [(AINV a, e)] stmp (Short "Some") env.
Definition EVAL_ECon_None :=
  fun (A : Type) (AINV : A -> val -> Prop) (stmp : stamp) (env : sem_env val) =>
    EVAL_ECon (option_INV A AINV None) [] [] stmp (Short "None") env.
GenerateMatchLemma option.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase [match_arg_v] matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase0 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateInvariant bool.
GenerateDeclaration bool.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_bool_cert_thm : core.
Definition EVAL_ECon_true := fun (stmp : stamp) (env : sem_env val) =>
                               EVAL_ECon (bool_INV true) [] [] stmp (Short "True") env.
Definition EVAL_ECon_false := fun (stmp : stamp) (env : sem_env val) =>
                                EVAL_ECon (bool_INV false) [] [] stmp (Short "False") env.
GenerateMatchLemma bool.
Proof.
  my_intros.
  handle_matched.
  destruct matched; destruct_inv Hinv_match.
  - solve_case Hcase (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.

  - solve_case Hcase0 (@nil val) matched_st.
    repeat normalize_fuels [matched_f; case_f].
    repeat handle_good_cons.
    final_solve.
Qed.

GenerateCertificate PeanoNat.Nat.eqb.
Proof.
  apply EVAL_remove_EQ; try repeat constructor.
  intro n.
  apply EVAL_ELetrec.
  induction n;
  intros v Hninv;
  apply EVAL_EFun; intros m v0 Hminv.
  - apply EVAL_EMat_nat with (match m with
                              | 0 => true
                              | S _ => false
                              end)
                             (fun n' => match m with
                                     | 0 => false
                                     | S m' => PeanoNat.Nat.eqb n' m'
                                     end) 0; try reflexivity.
    + good_cons_env_solve.
    + eapply EVAL_EVar.
      * unfold nsLookup; reflexivity.
      * assumption.
    + intros.
      apply EVAL_EMat_nat with true (fun _ => false) m; try reflexivity; try good_cons_env_solve.
      * eapply EVAL_EVar.
        -- unfold nsLookup; reflexivity.
        --  assumption.
      * intros. eapply EVAL_ECon_true.
        reflexivity.
        reflexivity.
        constructor.
        intros; simpl; inv H1; reflexivity.
      * intros. eapply EVAL_ECon_false.
        reflexivity.
        reflexivity.
        constructor.
        intros vals H'; simpl; inv H'; reflexivity.
    + intros.
      inv H.
  - normalize_env.
    apply EVAL_EMat_nat with
      (match m with
       | 0 => true
       | S _ => false
       end)
      (fun n' => match m with
              | 0 => false
              | S m' => PeanoNat.Nat.eqb n' m'
              end) (S n); try reflexivity; try good_cons_env_solve.
    * eapply EVAL_EVar.
      reflexivity.
      assumption.
    * intro wrong. inv wrong.
    * intros a0 v1 Heq Hsomeinv. apply EVAL_EMat_nat with
        false (fun m' => PeanoNat.Nat.eqb a0 m')
        m; try reflexivity; try good_cons_env_solve.
      -- eapply EVAL_EVar; try reflexivity; try assumption.
      -- intros. eapply EVAL_ECon_false; try reflexivity; try constructor.
         intros.
         inv H0. reflexivity.
      -- intros. eapply EVAL_EApp_Opapp.
         eapply EVAL_EApp_Opapp.
         eapply EVAL_ELetrec_EVAL_EVar.
         eapply EVAL_ELetrec.
         intros.
         apply IHn.
         apply H1.
         reflexivity.
         eapply EVAL_EVar; try reflexivity; try assumption.
         unfold EQ.
         split.
         inv Heq; reflexivity.
         assumption.
         eapply EVAL_EVar; try reflexivity; try assumption.
Qed.
GenerateDeclaration PeanoNat.Nat.eqb.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_eqb_cert_thm : core.

GenerateCertificate map_get_nat.
Proof.
  intros.
  apply EVAL_remove_EQ; try repeat constructor.
  intro m.
  apply EVAL_ELetrec.
  induction m;
  intros vm Hminv;
  apply EVAL_EFun; intros x vx Hxinv.
  - apply EVAL_EMat_list with
      _ (prod_INV nat B nat_INV B_INV) None
      (fun (p : nat * B) m' =>
         let (k,v) := p in
         if PeanoNat.Nat.eqb k x then Some v else map_get_nat m' x)
      []; try reflexivity; try good_cons_env_solve; try (intros;find_inversion).
    + eapply EVAL_EVar; try reflexivity; try assumption.
    + intros. eapply EVAL_ECon_None; try reflexivity; try (repeat constructor).
      intros vals HForall. inv HForall. reflexivity.
    + intros. inv H.
  - apply EVAL_EMat_list with
      _ (prod_INV nat B nat_INV B_INV) None
      (fun (p : nat * B) m' =>
         let (k,v) := p in
         if PeanoNat.Nat.eqb k x then Some v else map_get_nat m' x)
      (a::m); try reflexivity; try good_cons_env_solve; try find_inversion.
    + eapply EVAL_EVar; try reflexivity; try assumption.
    + intros. inv H.
    + intros. apply EVAL_EMat_prod with _ _ nat_INV B_INV
                (fun k v => if PeanoNat.Nat.eqb k x then Some v else map_get_nat a_1 x) a;
        try good_cons_env_solve.
      * inv H. reflexivity.
      * eapply EVAL_EVar; try reflexivity; try assumption.
        inv H.
        assumption.
      * intros.
        apply EVAL_EMat_bool with
          (Some a_3) (map_get_nat a_1 x) (PeanoNat.Nat.eqb a_2 x);
          try reflexivity; try good_cons_env_solve.
        -- eapply EVAL_EApp_Opapp.
           eapply EVAL_EApp_Opapp.
           eapply EVAL_ELetrec_EVAL_EVar.
           apply cake_eqb_certificate_thm.
           (* first failure with optimize *) (* issue with repeating constructors *)
           reflexivity.
           eapply EVAL_EVar; try reflexivity; try assumption.
           eapply EVAL_EVar; try reflexivity; try assumption.
        -- intros. eapply EVAL_ECon_Some.
           reflexivity.
           reflexivity.
           constructor.
           eapply EVAL_EVar; try reflexivity; try assumption.
           constructor.
           intros vals Hforall. inv Hforall.
           inv H10.
           simpl.
           eexists.
           split.
           reflexivity.
           assumption.
        -- intro Ha2_neq_x.
           eapply EVAL_EApp_Opapp.
           eapply EVAL_EApp_Opapp.
           eapply EVAL_EVar_Recclosure.
           reflexivity.
           intros.
           eapply IHm.
           apply H5.
           eapply EVAL_EVar; try reflexivity; try assumption.
           unfold EQ; split; try assumption.
           inv H; try reflexivity.
           eapply EVAL_EVar; try reflexivity; try assumption.
Qed.
GenerateDeclaration map_get_nat.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_map_get_nat_cert_thm : core.

Ltac quick_EVAL_EVar := eapply EVAL_EVar; try reflexivity; try assumption.

GenerateCertificate manifest_set_my_plc.
Proof.
  eapply EVAL_EFun.
  intros.
  eapply EVAL_EFun.
  intros.
  apply EVAL_EMat_Manifest with (fun _ oldasps old_app_asps oldKnowsOf oldContext oldTargets oldPolicy => {|
           my_abstract_plc := x;
           asps := oldasps;
           appraisal_asps := old_app_asps;
           uuidPlcs := oldKnowsOf;
           pubKeyPlcs := oldContext;
           targetPlcs := oldTargets;
           policy := oldPolicy
         |}) x0.
  reflexivity.
  (* HEAVILY DISLIKE FIX SOON *)
  Ltac dumb := match goal with
               | [H : ?x = ?y |- _] => try (inv H); dumb
               | [H : In ?s ?ls |- _] => try (inv H); dumb
               end.
  good_cons_env_solve; repeat dumb.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_ECon_Build_Manifest; try reflexivity; try repeat constructor; try quick_EVAL_EVar.
  intros vals HForall.
  inv HForall.
  inv H13.
  inv H14.
  inv H16.
  inv H18.
  inv H20.
  inv H22.
  inv H24.
  simpl.
  repeat eexists; try assumption.
Qed.

GenerateDeclaration manifest_set_my_plc.
Proof.
  simpl; unfold wrapped_eval; simpl; unfold DECL.
  exists 100.
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  simp pmatch; simpl.
  reflexivity.
Qed.
Local Hint Resolve DECL_indiv_manifest_set_my_plc_cert_thm : core.


GenerateCertificate empty_Manifest_Plc.
Proof.
  eapply EVAL_ECon_O; try reflexivity; try constructor.
  intros vals HForall. inv HForall. reflexivity.
Qed.
GenerateDeclaration empty_Manifest_Plc.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_empty_Manifest_Plc_cert_thm : core.

GenerateCertificate manifest_set_empty.
Proof.
  intros.
  eapply EVAL_ECon_nil. reflexivity. reflexivity.
  constructor.
  intros vals HForall. inv HForall. reflexivity.
Qed.
GenerateDeclaration manifest_set_empty.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_manifest_set_empty_cert_thm : core.

GenerateCertificate empty_PolicyT.
Proof.
  intros.
  eapply EVAL_ECon_nil; try reflexivity; try constructor.
  intros vals HForall. inv HForall. reflexivity.
Qed.
GenerateDeclaration empty_PolicyT.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_empty_PolicyT_cert_thm : core.

GenerateCertificate empty_Manifest.
Proof.
  eapply EVAL_ECon_Build_Manifest; try reflexivity; try constructor.
  quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor. quick_EVAL_EVar.
  constructor.
  intros vals HForall.
  inv HForall.
  inv H3.
  inv H4.
  inv H5.
  inv H6.
  inv H7.
  inv H8.
  inv H9.
  repeat eexists.
Qed.
GenerateDeclaration empty_Manifest.
Proof.
  thing.
  repeat (simp eval_or_match; simpl).
  reflexivity.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_empty_Manifest_cert_thm : core.

GenerateCertificate map_set.
Proof.
  intros.
  apply EVAL_remove_EQ; try repeat constructor.
  intro mapcnb.
  apply EVAL_ELetrec.
  induction mapcnb.
  - intros. eapply EVAL_EFun.
    intros. eapply EVAL_EFun.
    intros. eapply EVAL_EMat_list with (matched := []).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros. eapply EVAL_ECon_cons.
    reflexivity.
    reflexivity.
    constructor.
    eapply EVAL_ECon_pair; try reflexivity.
    constructor.
    quick_EVAL_EVar.
    constructor.
    quick_EVAL_EVar.
    constructor.
    intros vals HF.
    inv HF.
    inv H7.
    inv H9.
    repeat eexists.
    assumption.
    assumption.
    constructor.
    eapply EVAL_ECon_nil; try reflexivity.
    constructor.
    intros vals HF. inv HF.
    repeat eexists.
    constructor.
    intros vals HF. inv HF.
    inv H7.
    inv H9.
    destruct H5.
    destruct H3.
    destruct H3.
    destruct H4.
    repeat eexists.
    apply H3.
    assumption.
    assumption.
    intros a b c d wrong. inv wrong.
  - intros. eapply EVAL_EFun.
    intros. eapply EVAL_EFun.
    intros.
    apply EVAL_EMat_list
      with (prod nat B) (prod_INV nat B nat_INV B_INV) [(x,x0)]
           (fun (a : nat * B) mapcnb' => (let (hk, hv) := a in
                          if PeanoNat.Nat.eqb hk x
                          then (hk, x0) :: mapcnb'
                          else
                            (hk, hv)
                              :: (fix map_set (B0 : Type) (m : MapC nat B0) (x1 : nat) (v2 : B0) {struct m} :
                                MapC nat B0 :=
                                   match m with
                                   | [] => [(x1, v2)]
                                   | (hk0, hv0) :: t =>
                                       if PeanoNat.Nat.eqb hk0 x1
                                       then (hk0, v2) :: t
                                       else (hk0, hv0) :: map_set B0 t x1 v2
                                   end) B mapcnb' x x0))
           (a::mapcnb).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros.
    inv H2.
    intros.
    apply EVAL_EMat_prod with _ _ nat_INV B_INV
      (fun hk hv => if PeanoNat.Nat.eqb hk x
        then (hk, x0) :: a_1
        else
         (hk, hv)
         :: (fix map_set (B0 : Type) (m : MapC nat B0) (x1 : nat) (v2 : B0) {struct m} :
                 MapC nat B0 :=
               match m with
               | [] => [(x1, v2)]
               | (hk0, hv0) :: t =>
                   if PeanoNat.Nat.eqb hk0 x1
                   then (hk0, v2) :: t
                   else (hk0, hv0) :: map_set B0 t x1 v2
               end) B a_1 x x0) a_0.
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros. eapply EVAL_EMat_bool.
    reflexivity.
    good_cons_env_solve.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    apply cake_eqb_certificate_thm.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    intros. eapply EVAL_ECon_cons; try reflexivity.
    constructor.
    intros. eapply EVAL_ECon_pair; try reflexivity.
    constructor.
    quick_EVAL_EVar.
    constructor.
    quick_EVAL_EVar.
    constructor.
    intros vals HF.
    inv HF.
    inv H13.
    inv H14.
    repeat eexists; assumption.
    constructor.
    quick_EVAL_EVar.
    constructor.
    intros vals HF.
    inv HF.
    inv H13.
    inv H14.
    destruct H11.
    destruct H5.
    destruct H5.
    destruct H9.
    repeat eexists.
    apply H5.
    assumption.
    assumption.
    assumption.
    intros. eapply EVAL_ECon_cons.
    reflexivity.
    reflexivity.
    constructor.
    intros. eapply EVAL_ECon_pair.
    reflexivity.
    reflexivity.
    constructor.
    quick_EVAL_EVar.
    constructor.
    quick_EVAL_EVar.
    constructor.
    intros vals HF. inv HF.
    inv H13.
    inv H14.
    repeat eexists.
    assumption.
    assumption.
    constructor.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EVar_Recclosure.
    reflexivity.
    intros.
    apply IHmapcnb.
    apply H9.
    quick_EVAL_EVar.
    unfold EQ.
    split; try assumption.
    inv H2. reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    constructor.
    intros vals HF.
    inv HF.
    destruct H11.
    destruct H5.
    destruct H5.
    destruct H9.
    simpl.
    inv H13.
    inv H16.
    repeat eexists.
    assumption.
    assumption.
    assumption.
    Unshelve.
    exact B.
    exact B_INV.
    exact (fun _ _ => []). (* Where the hell does this one come from? *)
Qed.
GenerateDeclaration map_set.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_map_set_cert_thm : core.

GenerateCertificate manifest_update_env.
Proof.
  eapply EVAL_EFun.
  intros; eapply EVAL_EFun.
  intros; eapply EVAL_EFun.
  intros.
  apply EVAL_ELet with _ (match map_get_nat x0 x with
                          | Some mm => mm
                          | None => manifest_set_my_plc x empty_Manifest
                          end)
                       (fun m => let m' := x1 m in map_set x0 x m') Manifest_INV.
  reflexivity.
  intros.
  apply EVAL_EMat_option with
    _ Manifest_INV (fun mm => mm) (manifest_set_my_plc x empty_Manifest) (map_get_nat x0 x).
  reflexivity.
  good_cons_env_solve.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  eapply cake_map_get_nat_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros. quick_EVAL_EVar.
  intros. eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  eapply cake_manifest_set_my_plc_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  repeat eexists.
  intros.
  eapply EVAL_ELet.
  reflexivity.
  intros.
  eapply EVAL_EApp_Opapp.
  quick_EVAL_EVar.
  apply H1.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  (* eapply EVAL_optimize_ELetrec. (* This is admitted but seems to work *) *)
  eapply cake_map_set_certificate_thm.
  unfold nsLookup. simpl.
  (* HERE *)
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
Qed.

GenerateDeclaration manifest_update_env.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_manifest_update_env_cert_thm : core.

GenerateCertificate manset_add.
Proof.
  apply EVAL_ELetrec_noEQ.
  intros. eapply EVAL_remove_EQ; try repeat constructor.
  intros s. generalize dependent v. induction s; intros v H.
  - eapply EVAL_EFun.
    intros.
    inv H0.
    apply EVAL_EMat_list
      with _ nat_INV [n] (fun h t => if Nat.eqb n h then [] else h :: manset_add n t) [].
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros. eapply EVAL_ECon_cons.
    simpl.
    reflexivity.
    reflexivity.
    constructor.
    quick_EVAL_EVar.
    constructor.
    eapply EVAL_ECon_nil.
    reflexivity.
    reflexivity.
    constructor.
    intros.
    inv H3.
    reflexivity.
    constructor.
    intros.
    inv H3.
    inv H8.
    inv H10.
    simpl.
    do 2 eexists.
    split. reflexivity.
    split; try assumption; try reflexivity.
    intros i d d' k contra.
    inv contra.
  - eapply EVAL_EFun.
    intros.
    inv H0.
    inv H2.
    destruct H1 as [v1 [Hv0eqxv1 [Hinvx Hinvv1]]].
    apply EVAL_EMat_list
      with _ nat_INV [n] (fun h t => if Nat.eqb n h then (a::s) else h :: manset_add n t) (a::s).
    reflexivity.
    subst.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intro contra. inv contra.
    intros.
    apply EVAL_EMat_bool
      with (a::s) (a_0::manset_add n a_1) (Nat.eqb n a_0).
    reflexivity.
    good_cons_env_solve.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    apply cake_eqb_certificate_thm.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    intros.
    quick_EVAL_EVar.
    intros.
    eapply EVAL_ECon_cons.
    reflexivity.
    reflexivity.
    constructor.
    quick_EVAL_EVar.
    constructor.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EVar_Recclosure.
    reflexivity.
    intros.
    apply IHs.
    apply H6.
    quick_EVAL_EVar.
    unfold EQ;
      split; try reflexivity; try assumption.
    quick_EVAL_EVar.
    unfold EQ;
      split; try reflexivity; try assumption.
    inv H1. reflexivity.
    constructor.
    intros.
    inv H6.
    simpl.
    inv H11.
    inv H13.
    do 2 eexists.
    split; try reflexivity.
    split; try reflexivity; try assumption.
Qed.
GenerateDeclaration manset_add.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_manset_add_cert_thm : core.

GenerateCertificate update_manifest_policy_targ.
Proof.
  eapply EVAL_EFun.
  intros.
  eapply EVAL_EFun.
  intros.
  eapply EVAL_EFun.
  intros.
  eapply EVAL_EMat_Manifest.
  reflexivity.
  good_cons_env_solve.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_ECon_Build_Manifest.
  reflexivity.
  reflexivity.
  constructor.
  quick_EVAL_EVar.
  constructor.
  quick_EVAL_EVar.
  constructor.
  quick_EVAL_EVar.
  constructor.
  quick_EVAL_EVar.
  constructor.
  quick_EVAL_EVar.
  constructor.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  apply cake_manset_add_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  constructor.
  quick_EVAL_EVar.
  constructor.
  intros.
  simpl.
  inv H10.
  inv H15.
  inv H16.
  inv H18.
  inv H20.
  inv H22.
  inv H24.
  inv H26.
  do 7 eexists.
  subst.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
Qed.

GenerateDeclaration update_manifest_policy_targ.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_update_manifest_policy_targ_cert_thm : core.

GenerateCertificate aspid_manifest_update.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EMat_Manifest.
  reflexivity.
  good_cons_env_solve; try quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_ECon_Build_Manifest.
  reflexivity.
  reflexivity.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  apply cake_manset_add_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  intros.
  inv H9.
  inv H14.
  inv H15.
  inv H17.
  inv H19.
  inv H21.
  inv H23.
  inv H25.
  simpl.
  do 7 eexists.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
  split; try reflexivity; try assumption.
Qed.

GenerateDeclaration aspid_manifest_update.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_aspid_manifest_update_cert_thm : core.

GenerateCertificate sig_aspid.
Proof.
  eapply EVAL_ECon_O.
  reflexivity.
  reflexivity.
  constructor.
  intros.
  inv H.
  reflexivity.
Qed.

GenerateDeclaration sig_aspid.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_sig_aspid_cert_thm : core.

GenerateCertificate hsh_aspid.
Proof.
  eapply EVAL_ECon_O; try reflexivity.
  constructor.
  intros.
  inv H.
  reflexivity.
Qed.

GenerateDeclaration hsh_aspid.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_hsh_aspid_cert_thm : core.

GenerateCertificate enc_aspid.
Proof.
  eapply EVAL_ECon_O; try reflexivity.
  constructor.
  intros.
  inv H.
  reflexivity.
Qed.

GenerateDeclaration enc_aspid.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_enc_aspid_cert_thm : core.

GenerateCertificate pubkey_manifest_update.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EMat_Manifest.
  reflexivity.
  good_cons_env_solve.
  quick_EVAL_EVar.
  intros. eapply EVAL_ECon_Build_Manifest; try reflexivity.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  apply cake_manset_add_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  intros.
  inv H9.
  inv H14.
  inv H15.
  inv H17.
  inv H19.
  inv H21.
  inv H23.
  inv H25.
  simpl.
  do 7 eexists.
  repeat (split; try reflexivity; try assumption).
Qed.

GenerateDeclaration pubkey_manifest_update.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_pubkey_manifest_update_cert_thm : core.

GenerateCertificate asp_manifest_update.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros.
  apply EVAL_EMat_ASP
    with x0 x0 (fun _ _ params => match params with
                               | asp_paramsC i _ targp targid =>
                                   let m' := update_manifest_policy_targ targp targid x0
                                   in aspid_manifest_update i m'
                               end)
         (aspid_manifest_update Params_Admits.sig_aspid x0)
         (aspid_manifest_update Params_Admits.sig_aspid x0)
         (fun p => let m' := pubkey_manifest_update p x0
                in aspid_manifest_update Params_Admits.enc_aspid m')
         x.
  reflexivity.
  good_cons_env_solve.
  quick_EVAL_EVar.
  intros. quick_EVAL_EVar.
  intros. quick_EVAL_EVar.
  intros. apply EVAL_EMat_ASP_PARAMS
    with (fun i _ targp targid =>
            let m' := update_manifest_policy_targ targp targid x0 in aspid_manifest_update i m')
         a_2.
  reflexivity.
  good_cons_env_solve.
  quick_EVAL_EVar.
  intros. eapply EVAL_ELet.
  reflexivity.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_update_manifest_policy_targ_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_aspid_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_aspid_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_aspid_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_ELet.
  reflexivity.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_pubkey_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_aspid_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
Qed.

GenerateDeclaration asp_manifest_update.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_asp_manifest_update_cert_thm : core.

GenerateCertificate asp_manifest_generator.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EApp_Opapp.
  intros. eapply EVAL_EApp_Opapp.
  intros. eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  eapply cake_manifest_update_env_certificate_thm.
  constructor.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  intros. eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_asp_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
Qed.

GenerateDeclaration asp_manifest_generator.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_asp_manifest_generator_cert_thm : core.

GenerateCertificate knowsof_manifest_update.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EMat_Manifest.
  reflexivity.
  good_cons_env_solve.
  quick_EVAL_EVar.
  intros. eapply EVAL_ECon_Build_Manifest; try reflexivity.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_ELetrec_EVAL_EVar.
  apply cake_manset_add_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor; try quick_EVAL_EVar.
  constructor.
  intros.
  inv H9.
  inv H14.
  inv H15.
  inv H17.
  inv H19.
  inv H21.
  inv H23.
  inv H25.
  simpl.
  do 7 eexists.
  repeat (split; try reflexivity; try assumption).
Qed.

GenerateDeclaration knowsof_manifest_update.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_knowsof_manifest_update_cert_thm : core.

GenerateCertificate at_manifest_generator.
Proof.
  eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EFun.
  intros. eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_manifest_update_env_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
  quick_EVAL_EVar.
  eapply EVAL_EApp_Opapp.
  eapply EVAL_EFun_EVAL_EVar.
  apply cake_knowsof_manifest_update_certificate_thm.
  reflexivity.
  quick_EVAL_EVar.
Qed.

GenerateDeclaration at_manifest_generator.
Proof.
  thing.
  Unshelve.
  constructor.
Qed.
Local Hint Resolve DECL_indiv_at_manifest_generator_cert_thm : core.

GenerateCertificate manifest_generator'.
Proof.
  eapply EVAL_ELetrec_noEQ.
  intros p v Hinvp. eapply EVAL_remove_EQ; try (repeat constructor).
  intro t.
  generalize dependent v.
  generalize dependent p.
  induction t;
    intros; eapply EVAL_EFun;
    intros t' v' [Heqt' Hinvt'];
    eapply EVAL_EFun;
    intros env v0 Hinvenv;
    subst.
  - (* intros t' v' [Heqt' Hinvt']. *)
    (* eapply EVAL_EFun. *)
    (* intros env v0 Hinvenv. *)
    (* subst. *)
    eapply EVAL_EMat_Term
      with (fun a => asp_manifest_generator a p env)
           (fun q t0 => let e' := at_manifest_generator p q env in manifest_generator' q t0 e')
           (fun t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (asp a).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros. subst.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EFun_EVAL_EVar.
    apply cake_asp_manifest_generator_certificate_thm.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    do 4 intro. intro contra. inv contra.
    do 4 intro. intro contra. inv contra.
    do 6 intro. intro contra. inv contra.
    do 6 intro. intro contra. inv contra.
  - (* intros t' v' [Heqt' Hinvt']. *)
    (* eapply EVAL_EFun. *)
    (* intros env v0 Hinvenv. *)
    (* subst. *)
    eapply EVAL_EMat_Term
      with (fun a => asp_manifest_generator a p env)
           (fun q t0 => let e' := at_manifest_generator p0 q env in manifest_generator' q t0 e')
           (fun t1 t2 => manifest_generator' p0 t2 (manifest_generator' p0 t1 env))
           (fun _ t1 t2 => manifest_generator' p0 t2 (manifest_generator' p0 t1 env))
           (fun _ t1 t2 => manifest_generator' p0 t2 (manifest_generator' p0 t1 env))
           (att p t).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    intros.
    inv H.
    intros.
    eapply EVAL_ELet.
    reflexivity.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EFun_EVAL_EVar.
    apply cake_at_manifest_generator_certificate_thm.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    intros. eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar; try reflexivity.
    eapply EVAL_ELetrec_noEQ.
    apply IHt.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    split.
    inv H.
    reflexivity.
    assumption.
    quick_EVAL_EVar.
    do 4 intro; intro contra; inv contra.
    do 6 intro; intro contra; inv contra.
    do 6 intro; intro contra; inv contra.
  - eapply EVAL_EMat_Term
      with (fun a => asp_manifest_generator a p env)
           (fun q t0 => let e' := at_manifest_generator p q env in manifest_generator' q t0 e')
           (fun t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (lseq t1 t2).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    do 2 intro; intro contra; inv contra.
    do 4 intro; intro contra; inv contra.
    intros.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt2.
    apply H2.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    split; try reflexivity; try assumption.
    inv H. reflexivity.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt1.
    apply H2.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    inv H.
    split; try reflexivity; try assumption.
    quick_EVAL_EVar.
    do 6 intro; intro contra; inv contra.
    do 6 intro; intro contra; inv contra.
  - eapply EVAL_EMat_Term
      with (fun a => asp_manifest_generator a p env)
           (fun q t0 => let e' := at_manifest_generator p q env in manifest_generator' q t0 e')
           (fun t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (bseq s t1 t2).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    do 2 intro; intro contra; inv contra.
    do 4 intro; intro contra; inv contra.
    do 4 intro; intro contra; inv contra.
    intros.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt2.
    apply H3.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    inv H.
    split; try reflexivity; try assumption.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt1.
    apply H3.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    inv H.
    split; try reflexivity; try assumption.
    quick_EVAL_EVar.
    do 6 intro; intro contra; inv contra.
  - eapply EVAL_EMat_Term
      with (fun a => asp_manifest_generator a p env)
           (fun q t0 => let e' := at_manifest_generator p q env in manifest_generator' q t0 e')
           (fun t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (fun _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 env))
           (bpar s t1 t2).
    reflexivity.
    good_cons_env_solve.
    quick_EVAL_EVar.
    do 2 intro; intro contra; inv contra.
    do 4 intro; intro contra; inv contra.
    do 4 intro; intro contra; inv contra.
    do 6 intro; intro contra; inv contra.
    intros.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt2.
    apply H3.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    inv H.
    split; try reflexivity; try assumption.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_EApp_Opapp.
    eapply EVAL_ELetrec_EVAL_EVar.
    eapply EVAL_ELetrec_noEQ.
    intros.
    apply IHt1.
    apply H3.
    reflexivity.
    quick_EVAL_EVar.
    quick_EVAL_EVar.
    inv H.
    split; try reflexivity; try assumption.
    quick_EVAL_EVar.
Qed.
GenerateDeclaration manifest_generator'.
Proof. next_decl. Qed.
Local Hint Resolve DECL_indiv_manifest_generator'_cert_thm : core.

FinishProgram "manifestGeneratorProg".
Proof.
  repeat (next_decl; auto).
  simpl.
  repeat (next_decl; auto).
  simpl.
  next_decl; auto.
  next_decl; auto.
  next_ddecl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl; auto.
  next_decl. apply DECL_indiv_eqb_cert_thm.
  next_decl. apply DECL_indiv_map_get_nat_cert_thm.
  next_decl. apply DECL_indiv_manifest_set_my_plc_cert_thm.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl. auto.
  next_decl; auto.




  reflexivity.
Qed.

(* Finished in 30 mins post declarations filling *)
  (* died :( *)
  (* Problem: idk but probably too many extend dec envs at once *)
  (* Solution: do what the HOL folks do and turn those into terms that don't unfold? *)


(* LETS GOOOOOOOOOOOO *)
