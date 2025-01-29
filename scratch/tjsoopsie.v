Fixpoint free_vars (e:exp) (bound : list (ident string string)) : list (ident string string) :=
  match e with
  | ERaise e' => free_vars e' bound
  | EHandle e' pes =>
      free_vars e' bound ++
                fold_right (@app (ident string string)) []
                (map (fun '(p,e'') => free_vars e'' (map Short (pat_bindings p []))) pes)
  | ELit _ => []
  | ECon _ es => fold_right (@app (ident string string)) [] (map (fun e' => free_vars e' bound) es)
  | EVar id => if existsb (fun i => ident_string_beq id i) bound then
                []
              else [id]
  | EFun var e' => free_vars e' ((Short var)::bound)
  | EApp _ es => fold_right (@app (ident string string)) [] (map (fun e' => free_vars e' bound) es)
  | ELog _ e1 e2 => free_vars e1 bound ++ free_vars e2 bound
  | EIf e0 e1 e2 => free_vars e0 bound ++ free_vars e1 bound ++ free_vars e2 bound
  | EMat e' pes =>
      free_vars e' bound ++
                fold_right (@app (ident string string)) []
                (map (fun '(p,e'') => free_vars e'' (map Short (pat_bindings p []))) pes)
  | ELet None e1 e2 => free_vars e1 bound ++ free_vars e2 bound
  | ELet (Some id) e1 e2 => free_vars e1 ((Short id)::bound) ++ free_vars e2 ((Short id)::bound)
  | ELetrec funcs e' =>
      let fun_names := map (fun '(fid,_,_) => Short fid) funcs in
      free_vars e' (fun_names ++ bound) ++
                fold_right (@app (ident string string)) []
                (map (fun '(_,var,body) => free_vars body ((Short var)::(fun_names ++ bound))) funcs)
  | ETannot e' _ | ELannot e' _ => free_vars e' bound
  end.


Fixpoint remove_dup_ids (ids : list (ident string string)) seen : list (ident string string) :=
    match ids with
    | [] => seen
    | id::ids' => if existsb (fun i => ident_string_beq id i) seen
                then remove_dup_ids ids' seen
                else remove_dup_ids ids' (id::seen)
    end.

Fixpoint gather_values env_sev frees : env_val :=
  match frees with
  | [] => nsEmpty
  | freev::frees' =>
      match nsLookup ident_string_beq freev env_sev with
      | None => gather_values env_sev frees'
      | Some v => (freev,v)::(gather_values env_sev frees')
      end
  end.

Definition optimize_recclosure_env (e : exp) (env : sem_env val) : sem_env val :=
  let fvs := remove_dup_ids (free_vars e []) [] in
  let env_sev := sev env in
  update_sev env (gather_values env_sev fvs).

From Equations Require Import Equations.
Require Import StructTact.StructTactics.

Lemma nsLookup_cover : forall V id x y (v : V),
  nsLookup ident_string_beq id x = Some v ->
  nsLookup ident_string_beq id (x ++ y) = Some v.
Proof.
  induction x; intros.
  - inv H.
  - unfold nsLookup in *. simpl in *.
    destruct a.
    break_if.
    assumption.
    apply IHx.
    assumption.
Qed.

Lemma opti_somethin : forall id envv v fvs fvs',
  nsLookup ident_string_beq id (gather_values envv fvs) = Some v ->
  nsLookup ident_string_beq id (gather_values envv (fvs ++ fvs')) = Some v.
Proof.
  induction fvs; intros.
  - inv H.
  - simpl in *.
    break_match.
    unfold nsLookup in *. simpl in *.
    break_if.
    assumption.
    apply IHfvs.
    assumption.
    apply IHfvs.
    assumption.
Qed.

Lemma ident_string_beq_refl : forall id, ident_string_beq id id = true.
Proof.
  induction id.
  - simpl.
    apply eqb_refl.
  - simpl.
    rewrite eqb_refl.
    rewrite IHid.
    reflexivity.
Qed.

Lemma ident_string_beq_iff_false : forall id id', ident_string_beq id id' = false <-> id <> id'.
Proof.
  split;
    generalize dependent id';
    induction id; destruct id'; simpl.
  - intros.
    rewrite eqb_neq in H.
    intro contra.
    inv contra.
    contradiction H. reflexivity.
  - intros dc wrong. inv wrong.
  - intros dc wrong. inv wrong.
  - intros.
    intro contra.
    inversion contra.
    eapply IHid.
    rewrite H1 in H.
    rewrite eqb_refl in H. simpl in H.
    apply H.
    apply H2.
  - intro contra.
    rewrite eqb_neq.
    intro contra2.
    contradiction contra.
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros.
    remember (x =? s) as fp.
    destruct fp.
    symmetry in Heqfp.
    rewrite eqb_eq in Heqfp.
    subst.
    simpl.
    apply IHid.
    intro contra.
    contradiction H.
    subst; reflexivity.
    reflexivity.
Qed.

Lemma ident_string_beq_iff_true : forall id id', ident_string_beq id id' = true <-> id = id'.
Proof.
  split;
    generalize dependent id';
    generalize dependent id;
    induction id; destruct id'; intros; try inv H.
  - simpl in H.
    apply f_equal.
    apply eqb_eq; assumption.
  - rewrite Bool.andb_true_iff in H1.
    destruct H1.
    apply f_equal2.
    rewrite eqb_eq in H0. assumption.
    apply IHid.
    assumption.
  - apply ident_string_beq_refl.
  - apply ident_string_beq_refl.
Qed.

Lemma ident_string_beq_sym : forall id id', ident_string_beq id id' = ident_string_beq id' id.
Proof.
  unfold ident_string_beq.
  induction id; simpl.
  destruct id'; simpl; try reflexivity.
  apply eqb_sym.
  destruct id'; simpl; try reflexivity.
  rewrite IHid.
  rewrite eqb_sym.
  reflexivity.
Qed.

Lemma in_exists_eq : forall (A : Type) (eqb : A -> A -> bool) (a : A) l,
    (forall x, eqb x x = true) ->
    (forall x y, eqb x y = true <-> x = y) ->
    existsb (fun a' => eqb a a') l = true <-> In a l.
Proof.
  split;
    generalize dependent A.
  - induction l.
    + intros.
      inv H1.
    + intros.
      simpl in *.
      remember (eqb a a0) as eqa0.
      destruct eqa0.
      symmetry in Heqeqa0.
      rewrite H0 in Heqeqa0.
      symmetry in Heqeqa0.
      left.
      assumption.
      simpl in *.
      right.
      apply IHl. assumption.
      assumption.
      assumption.
  - induction l; intros.
    + inv H1.
    + simpl in H1.
      destruct H1.
      * simpl.
        subst.
        rewrite H.
        reflexivity.
      * simpl.
        apply IHl in H1; try assumption.
        rewrite H1. simpl.
        apply Bool.orb_true_r.
Qed.

Lemma not_in_exists_eq : forall (A : Type) (eqb : A -> A -> bool) (a : A) l,
    (forall x, eqb x x = true) ->
    (forall x y, eqb x y = false <-> x <> y) ->
    existsb (fun a' => eqb a a') l = false <-> ~ In a l.
Proof.
  split; generalize dependent A; induction l; intros.
  - intro contra. inv contra.
  - intro contra.
    destruct contra. subst.
    simpl in H1.
    rewrite H in H1. inv H1.
    simpl in H1.
    rewrite Bool.orb_false_iff in H1.
    destruct H1.
    apply IHl; try assumption.
  - reflexivity.
  - simpl.
    rewrite Bool.orb_false_iff.
    assert (a <> a0).
    intro contra.
    apply H1.
    left. subst. reflexivity.
    split.
    rewrite H0.
    assumption.
    apply IHl; try assumption.
    intro contra.
    contradiction H1.
    right. assumption.
Qed.

Lemma idk_still : forall a l' l, In a l' -> remove_dup_ids (a::l) l' = remove_dup_ids l (l').
Proof.
  induction l'; intros.
  - inv H.
  - simpl in *.
    destruct (Namespace.ident_eq_dec string string string_dec string_dec a0 a).
    + subst. rewrite ident_string_beq_refl.
      simpl. reflexivity.
    + destruct H.
      * apply n in H. contradiction H.
      * rewrite <- ident_string_beq_iff_false in n.
        rewrite ident_string_beq_sym.
        rewrite n.
        simpl.
        rewrite <- in_exists_eq in H.
        rewrite H.
        reflexivity.
        apply ident_string_beq_refl.
        apply ident_string_beq_iff_true.
Qed.

Lemma opti_somethin''r : forall l l' a,
    In a l' -> In a (remove_dup_ids l l').
Proof.
  induction l; intros.
  - simpl. assumption.
  - simpl.
    remember (existsb (fun i => ident_string_beq a i) l') as thing.
    destruct thing.
    + apply IHl. assumption.
    + apply IHl.
      simpl. right. assumption.
Qed.

Lemma opti_somethin''l : forall l l' a,
    In a l -> In a (remove_dup_ids l l').
Proof.
  induction l; intros.
  - inv H.
  - simpl.
    remember (existsb (fun i => ident_string_beq a i) l') as thing.
    destruct H.
    + subst a0.
      destruct thing.
      apply opti_somethin''r.
      rewrite <- in_exists_eq.
      rewrite Heqthing.
      reflexivity.
      apply ident_string_beq_refl.
      apply ident_string_beq_iff_true.
      apply opti_somethin''r.
      left. reflexivity.
    + destruct thing.
      apply IHl.
      assumption.
      apply IHl.
      assumption.
Qed.

Lemma blublub : forall l envv id v,
  nsLookup ident_string_beq id (gather_values envv l) = Some v ->
  In id l.
Proof.
  induction l; intros.
  - simpl in *. inv H.
  - simpl in *.
    remember (nsLookup ident_string_beq a envv) as eqa.
    destruct eqa.
    unfold nsLookup in H.
    unfold lookup in H.
    remember (ident_string_beq id a) as ida.
    destruct ida.
    symmetry in Heqida.
    rewrite ident_string_beq_iff_true in Heqida.
    left. subst. reflexivity.
    right.
    eapply IHl.
    apply H.
    right.
    eapply IHl.
    apply H.
Qed.

Lemma nsLookup_iff_id_In_env : forall (envv : env_val) id,
  (exists v, nsLookup ident_string_beq id envv = Some v) <->
  In id (map fst envv).
Proof.
  split.
  induction envv; simpl in *; intros.
  - inv H.
    inv H0.
  - destruct a.
    unfold nsLookup in H.
    simpl in *.
    remember (ident_string_beq id i ) as idi.
    destruct idi.
    symmetry in Heqidi.
    rewrite ident_string_beq_iff_true in Heqidi.
    left. subst. reflexivity.
    right. eapply IHenvv.
    apply H.
  - induction envv.
    intros.
    inv H.
    destruct a.
    intros.
    simpl in H.
    destruct H. subst.
    unfold nsLookup in *; simpl in *.
    rewrite ident_string_beq_refl.
    exists v. reflexivity.
    unfold nsLookup in *; simpl in *.
    destruct (Namespace.ident_eq_dec _ _ string_dec string_dec id i).
    subst.
    rewrite ident_string_beq_refl.
    exists v. reflexivity.
    rewrite <- ident_string_beq_iff_false in n.
    rewrite n.
    apply IHenvv.
    assumption.
Qed.

Lemma blublublublub : forall l (envv : env_val) id v,
  nsLookup ident_string_beq id (gather_values envv l) = Some v ->
  In id (map fst envv).
Proof.
  induction l; intros.
  - inv H.
  - unfold nsLookup in H.
    simpl in *.
    remember (nsLookup ident_string_beq a envv) as lookupa.
    destruct lookupa.
    simpl in *.
    remember (ident_string_beq id a) as ida.
    destruct ida.
    symmetry in Heqida.
    rewrite ident_string_beq_iff_true in Heqida.
    eapply nsLookup_iff_id_In_env.
    symmetry in Heqlookupa.
    subst.
    eexists.
    apply Heqlookupa.
    eapply IHl.
    apply H.
    eapply IHl.
    apply H.
Qed.

Lemma gather_values_empty_namespace : forall l, gather_values [] l = [].
Proof.
  induction l; simpl; try reflexivity; try assumption.
Qed.


Lemma idk_yet : forall id envv a l,
    id <> a ->
    nsLookup ident_string_beq id (gather_values envv (a :: l)) =
      nsLookup ident_string_beq id (gather_values envv l).
Proof.
  intros.
  simpl in *.
  break_match.
  unfold nsLookup in *; simpl in *.
  rewrite <- ident_string_beq_iff_false in H.
  rewrite H.
  reflexivity.
  reflexivity.
Qed.

Lemma eureka : forall id envv l,
  (exists v, nsLookup ident_string_beq id (gather_values envv l) = Some v) <->
  In id (map fst envv) /\ In id l.
Proof.
  split.
  split.
  destruct H.
  eapply blublublublub. apply H.
  destruct H.
  eapply blublub. apply H.
  intros.
  generalize dependent envv.
  generalize dependent l.
  induction l; intros.
  - destruct H. inv H0.
  - destruct H.
    destruct H0.
    + subst.
      rewrite <- nsLookup_iff_id_In_env in H.
      destruct H.
      simpl.
      rewrite H.
      exists x.
      unfold nsLookup. simpl.
      rewrite ident_string_beq_refl.
      reflexivity.
    + unfold nsLookup in *; simpl in *.
      break_match.
      simpl.
      break_if.
      exists v. reflexivity.
      apply IHl.
      split; assumption.
      apply IHl.
      split; assumption.
Qed.

Lemma In_gather_In_env :
  forall l envv id v,
    In (id,v) (gather_values envv l) -> In id (map fst envv).
Proof.
  induction l; intros.
  - inv H.
  - simpl in *.
    break_match.
    simpl in *.
    destruct H.
    subst. simpl.
    eapply nsLookup_iff_id_In_env.
    exists v.
    inv H.
    assumption.
    eapply IHl.
    apply H.
    eapply IHl.
    apply H.
Qed.

Lemma In_gather_In_l :
  forall l envv id v,
    In (id,v) (gather_values envv l) -> In id l.
Proof.
  induction l; intros.
  inv H.
  simpl in *.
  break_match.
  simpl in H.
  destruct H.
  subst.
  left. inv H. reflexivity.
  right. eapply IHl. apply H.
  right. eapply IHl. apply H.
Qed.

Theorem wrong : forall l id v envv ,
    nsLookup ident_string_beq id envv = Some v /\
    In id l <->
    In (id,v) (gather_values envv l).
Proof.
  split;
    revert l envv.
  - induction l; intros.
    + destruct H. inv H0.
    + simpl in *.
      destruct H.
      destruct H0. subst.
      rewrite H.
      simpl.
      left; reflexivity.
      simpl in *.
      break_match.
      simpl.
      right.
      apply IHl.
      split; assumption.
      apply IHl.
      split; assumption.
  - induction l; intros.
    + inv H.
    + split.
      simpl in *.
      break_match.
      destruct H.
      inv H.
      assumption.
      apply IHl in H. destruct H. assumption.
      apply IHl in H. destruct H. assumption.
      simpl in *.
      break_match.
      destruct H.
      inv H.
      left; reflexivity.
      right.
      apply IHl in H. destruct H. assumption.
      right.
      apply IHl in H. destruct H. assumption.
Qed.

Ltac copy H :=
  match type of H with
  | ?anything =>
      assert anything by apply H
  end.

Ltac andtogether H H' :=
  match type of H with
  | ?anything =>
      match type of H' with
      | ?anything' => assert (anything /\ anything') by (split; assumption)
      end
  end.

Lemma In_remove_true : forall l x, In x (remove_dup_ids l [x]).
Proof.
  induction l; intros.
  - left. reflexivity.
  - apply opti_somethin''r.
    left. reflexivity.
Qed.

Definition id_dec x y := Namespace.ident_eq_dec _ _ string_dec string_dec x y.

Lemma idk : forall l x l', ~ In x l' ->
            In x (remove_dup_ids l l') ->
            In x l.
Proof.
  induction l; intros.
  simpl in *.
  contradiction H.
  simpl in *.
  break_if.
  rewrite in_exists_eq in Heqb.
  right.
  eapply IHl.
  apply H.
  assumption.
  apply ident_string_beq_refl.
  apply ident_string_beq_iff_true.
  rewrite not_in_exists_eq in Heqb.
  Check idk_still.
  destruct (id_dec x a).
  subst.
  left; reflexivity.
  right.
  assert (~ In x (a::l')).
  intro contra. simpl in contra.
  destruct contra.
  contradiction n.
  auto.
  contradiction H.
  eapply IHl.
  apply H1.
  assumption.
  apply ident_string_beq_refl.
  apply ident_string_beq_iff_false.
Qed.

Lemma idk' : forall l x, In x (remove_dup_ids l []) -> In x l.
Proof.
  induction l; intros.
  inv H.

  destruct (id_dec a x).
  left. auto.
  apply idk with [].
  intro contra.
  inv contra.
  assumption.
Qed.

Lemma simple_remove_dup : forall x l, In x l <-> In x (remove_dup_ids l []).
Proof.
  induction l;
    split; intros.
  - inv H.
  - inv H.
  - destruct H.
    + subst.
      apply In_remove_true.
    + simpl.
      destruct (id_dec x a).
      subst.
      apply In_remove_true.
      apply opti_somethin''l.
      assumption.
  - apply idk'.
    assumption.
Qed.

Lemma In_gather_entails_lookup_val : forall l a v envv,
    In (a, v) (gather_values envv l) ->
    nsLookup ident_string_beq a envv = Some v.
Proof.
  induction l; intros.
  - inv H.
  - simpl in *.
    break_match.
    simpl in *.
    destruct H.
    inv H.
    assumption.
    apply IHl.
    assumption.
    apply IHl.
    assumption.
Qed.

Lemma In_gather_entails_lookup_gather : forall l a v envv,
    In (a, v) (gather_values envv l) ->
    nsLookup ident_string_beq a (gather_values envv l) = Some v.
Proof.
  intros.
  copy H.
  apply In_gather_entails_lookup_val in H0.
  unfold nsLookup in *.
  simpl in *.
  generalize dependent a.
  revert l envv v.
  induction l; intros.
  - inv H.
  - simpl in *.
    break_match.
    simpl in *.
    destruct H.
    inv H.
    rewrite ident_string_beq_refl.
    reflexivity.
    simpl in *.
    break_if.
    rewrite ident_string_beq_iff_true in Heqb; subst.
    rewrite <- Heqo.
    rewrite <- H0.
    reflexivity.
    apply IHl. assumption.
    assumption.
    apply IHl; try assumption.
Qed.

Lemma In_gather_iff_In_gather_remove_l : forall l p envv,
  In p (gather_values envv l) <->
    In p (gather_values envv (remove_dup_ids l [])).
Proof.
  split; revert l envv p.
  - induction l; intros.
    + inv H.
    + destruct p.
      copy H.
      copy H.
      apply wrong in H.
      apply wrong.
      split.
      destruct H. assumption.
      apply opti_somethin''l.
      destruct H.
      assumption.
  - induction l; intros.
    + inv H.
    + destruct p.
      apply wrong.
      copy H.
      apply In_gather_In_l in H.
      rewrite <- simple_remove_dup in H.
      split; try assumption.
      destruct (id_dec i a); subst.
      eapply In_gather_entails_lookup_val.
      apply H0.
      eapply In_gather_entails_lookup_val.
      apply H0.
Qed.

Lemma eureka' : forall (id : ident tvarN tvarN) (envv : namespace tvarN tvarN val)
                  (l : list (ident tvarN tvarN)) v,
    nsLookup ident_string_beq id (gather_values envv l) = Some v ->
    In id (map fst envv) /\ In id l.
Proof.
  intros.
  apply eureka.
  exists v.
  assumption.
Qed.

Lemma eureka'' : forall l id envv v,
    nsLookup ident_string_beq id (gather_values envv l) = Some v ->
    In (id,v) (gather_values envv l).
Proof.
  induction l; intros.
  - inv H.

  - simpl in *.
    break_match.
    unfold nsLookup in *.
    simpl in *.
    break_if.
    rewrite ident_string_beq_iff_true in Heqb; subst.
    inv H.
    left; reflexivity.
    right.
    apply IHl.
    assumption.
    apply IHl.
    assumption.
Qed.


Lemma opti_somethin'' : forall l id envv v,
    nsLookup ident_string_beq id (gather_values envv l) = Some v ->
    nsLookup ident_string_beq id (gather_values envv (remove_dup_ids l [])) = Some v.
Proof.
  induction l; intros.
  - inv H.
  - destruct (Namespace.ident_eq_dec _ _ string_dec string_dec id a); subst.
    Check idk_yet.
    Check wrong.
    copy H.
    apply eureka' in H.
    destruct H.
    Check wrong.
    simpl in H0.
    break_match.
    copy H0.
    simpl in H2.
    unfold nsLookup in H2.
    simpl in H2.
    rewrite ident_string_beq_refl in H2.
    inv H2.
    Check idk_still.
    Check In_gather_iff_In_gather_remove_l.
    Check eureka'.
    apply In_gather_entails_lookup_gather.
    rewrite <- In_gather_iff_In_gather_remove_l.
    simpl.
    rewrite Heqo.
    left. reflexivity.
    apply In_gather_entails_lookup_gather.
    rewrite <- In_gather_iff_In_gather_remove_l.
    simpl.
    rewrite Heqo.
    apply eureka''.
    assumption.
    copy H.
    apply eureka' in H.
    destruct H.
    Check wrong.
    apply In_gather_entails_lookup_gather.
    rewrite <- In_gather_iff_In_gather_remove_l.
    apply eureka''.
    assumption.
Qed.

Theorem idk_yet' : forall e id env v,
    In id (free_vars e []) ->
    nsLookup ident_string_beq id (sev env) = Some v ->
    nsLookup ident_string_beq id (sev (optimize_recclosure_env e env)) = Some v.
Proof.
  unfold optimize_recclosure_env; simpl.
  intros. apply opti_somethin''.
    apply In_gather_entails_lookup_gather.
    Check eureka.
    apply wrong.
    split; try assumption.
Qed.

Check evaluate.
Theorem idk_fuck_me_Ihatemyselfwhycantisolvethisstupidproblemfuckfuckfuck :
  forall e f st (env : sem_env val),
    evaluate [e] f st env =
      evaluate [e] f st (optimize_recclosure_env e env).
Proof.
  unfold evaluate.
  induction e; intros.
  - simp eval_or_match in *.
    rewrite IHe.
    unfold optimize_recclosure_env.
    simpl.
    reflexivity.
  - induction X.
    + simp eval_or_match; simpl.
      unfold optimize_recclosure_env in *.
      unfold update_sev in *.
      simpl.
      rewrite app_nil_r.
      unfold update_sev.
      rewrite IHe.
      unfold eval_or_match_unfold_clause_4.
      break_match.
      break_match.
      reflexivity.
      break_match.
      simp eval_or_match.
      reflexivity.
      reflexivity.
    + destruct x.
      simpl in *.
      clear X.
      simp eval_or_match; simpl.
      simp eval_or_match in IHX; simpl in IHX.
      unfold eval_or_match_unfold_clause_4 in *.
      break_match.
      break_match.
      unfold optimize_recclosure_env, update_sev in *.
      (* HERE *)


      break_match.
      break_match.
      break_match.
      break_match.
      subst.
      Admitted.





Theorem EVAL_optimize_ELetrec :
  forall (A B : Type) (env : sem_env val) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fname var : varN) (body : exp),
    EVAL env (ELetrec [(fname,var,body)] (EVar (Short fname))) ((FUNC AINV BINV) f) ->
    EVAL (optimize_recclosure_env body env) (ELetrec [(fname,var,body)] (EVar (Short fname))) ((FUNC AINV BINV) f).
Proof.
  unfold EVAL, evaluate.
  intros.
  specialize (H st).
  destruct H as [v [fH [st' [Heval Hinv]]]].
  do 3 eexists.
  simp eval_or_match in *; simpl in *.
  unfold build_rec_env in *; simpl in *.
  unfold nsLookup in *; simpl in *.
  unfold update_sev in *; simpl in *.
  unfold nsBind in *; simpl in *.
  break_if.
  simpl in *.
  split.
  reflexivity.
  unfold FUNC in *.
  intros.
  specialize (Hinv x v0 H).
  destruct Hinv as [u [HBinvu Happ_returns]].
  exists u.
  split.
  assumption.
  unfold app_returns in *.
  intros.
  specialize (Happ_returns v1 H0 st0).
  destruct Happ_returns as [Henv [Hexp [Hst [Hu [Hdoapp [Heval_rel HBinvu']]]]]].
  inv Heval.
  eexists.
  unfold do_opapp in *.
  break_if.
  simpl in *.
  exists body, Hst, Hu.
  break_if.
  unfold update_sev.
  unfold build_rec_env.
  simpl.
  unfold nsBind.
  split.
  reflexivity.
  unfold eval_rel in *.
  unfold evaluate in *.
  destruct Heval_rel as [Hf Heval_rel].
  inv Hdoapp.
  unfold update_sev, nsBind, build_rec_env in *. simpl in *.
  split; try assumption.
  exists Hf.
  clear H H0 Hdoapp Heval HBinvu HBinvu' v0 Heqb0.
  revert Heval_rel.
  revert Hf st0 Hst Hu.
  induction Hexp; intros.
  intros.
  simp eval_or_match in *; simpl in *.
  unfold optimize_recclosure_env in *.
  unfold update_sev in *.
  simpl in *.
Admitted.
