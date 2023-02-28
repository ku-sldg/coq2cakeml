Require Import CakeSem.Utils.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import CakeSem.EvaluateTheory.

From Equations Require Import Equations.
Require Import StructTact.StructTactics.

Require Import Lia.
Require Import Lists.List.
Import ListNotations.

Definition ST := nat.

(* environment manipulation *)
Definition bind_variable_name name v (env : sem_env val) := update_sev env (nsBind name v (sev env)).

(* Certificate theorem for CakeML expressions *)

Definition EVAL (env : sem_env val) (e : exp) (inv : val -> Prop) :=
 forall st, exists v f st', evaluate [e] f st env = (st', Rval [v]) /\ inv v.

Definition eval_rel (st : state ST) (env : sem_env val) (e : exp) (st' : state ST) (v : val) : Prop :=
  exists (f : nat), evaluate [e] f st env = (st', Rval [v]).

Definition app_returns (P Q : val -> Prop) (cl : val) :=
  forall (v : val), P v ->
               forall (st : state ST), exists env exp st' u,
                 do_opapp [cl;v] = Some (env,exp) /\
                   eval_rel st env exp st' u /\
                   Q u.

Definition FUNC {A B : Type} (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (cl : val) :=
  forall x v, AINV x v -> exists u, BINV (f x) u /\ app_returns (AINV x) (BINV (f x)) cl.

Theorem EVAL_EFun {A B : Type} (env : sem_env val) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (n : varN) (body : exp) :
  (forall (x : A) (v : val), AINV x v -> EVAL (bind_variable_name n v env) body (BINV (f x))) ->
  EVAL env (EFun n body) ((FUNC AINV BINV f)).
Proof.
  unfold FUNC, EVAL, evaluate, app_returns, eval_rel.
  intros H_body st.
  do 3 eexists.
  split; try (simp eval_or_match; reflexivity).
  intros x v H_AINV_x_v.
  destruct (H_body x v H_AINV_x_v st) as [v' [f' [st' [eval_body H_BINV_fx_v']]]].
  eexists.
  split; try apply H_BINV_fx_v'.
  intros v0 H_AINV_x_v0 st0.
  destruct (H_body x v0 H_AINV_x_v0 st0) as [v'' [f'' [st'' [eval_body' H_BINV_fx_v'']]]].
  eexists.
  exists body.
  exists st''.
  exists v''.
  split; try reflexivity.
  split; try apply H_BINV_fx_v''.
  exists f''.
  unfold evaluate.
  assumption.
  Unshelve.
  constructor.
Qed.

Theorem EVAL_ELetrec_general : forall funs env exp P,
  NoDup (map (fun '(x,y,z) => x) funs) ->
  EVAL (update_sev env (build_rec_env funs env (sev env))) exp P ->
  EVAL env (ELetrec funs exp) P.
Proof.
  unfold EVAL, evaluate.
  intros funs env exp P HNoDup Hexp st.
  specialize (Hexp st).
  destruct Hexp as [v [f [st' [Hexp Hinv]]]].
  exists v. exists f. exists st'.
  split; try assumption.
  - simp eval_or_match.
    break_match; try assumption; try contradiction.
Qed.

(* EQ restricts an invariant to talk about a specific term *)
Definition EQ {A : Type} (AINV : A -> val -> Prop) (a : A) := fun a' v => (a = a') /\ AINV a' v.

Theorem EVAL_EQ {A : Type} : forall (AINV : A -> val -> Prop) (a : A) (e : exp) (env : sem_env val),
  EVAL env e (AINV a) -> EVAL env e ((EQ AINV a) a).
Proof.
  unfold EVAL.
  unfold EQ.
  intros AINV a e env H st.
  specialize (H st).
  destruct H as [v [f [st' [Heval Hinv]]]].
  exists v. exists f. exists st'.
  auto.
Qed.

Theorem exists_EQ_INV_iff_INV : forall (A : Type) (AINV : A -> val -> Prop) a v, (exists a', EQ AINV a' a v) <-> AINV a v.
Proof.
  unfold EQ.
  intros A AINV a v.
  split; intro H.
  destruct H as [a' [Ha'eqa HAINVa]].
  auto.
  exists a.
  split; auto.
Qed.

Theorem use_maximum_fuel : forall fuels es fuel st env st' vs,
    fuel <= list_max fuels ->
    eval_or_match true es fuel st env uu uu = (st', Rval vs) ->
    eval_or_match true es (list_max fuels) st env uu uu = (st', Rval vs).
Proof.
  induction fuels; intros.
  - inv H.
    assumption.
  - inv H.
    assumption.
    simpl.
    rewrite <- H1.
    unfold list_max in H.
    simpl in H.
    unfold list_max in H1.
    rewrite <- H1 in H.
    eapply more_fuel_same_value.
    apply H.
    assumption.
Qed.

Theorem in_max_le : forall (n : nat) (ns : list nat), In n ns -> n <= list_max ns.
Proof.
  intros n ns H.
  induction ns.
  inv H.
  unfold list_max.
  inv H.
  simpl.
  apply PeanoNat.Nat.le_max_l.
  simpl.
  apply IHns in H0.
  destruct (PeanoNat.Nat.max_dec a (fold_right Nat.max 0 ns)).
  rewrite e.
  rewrite PeanoNat.Nat.max_l_iff in e.
  unfold list_max in H0.
  lia.
  rewrite e.
  unfold list_max in H0. lia.
Qed.

Theorem evaluate_fuel_replacement : forall es es' fuel fuel' st st' env env' fin_st fin_st' vs vs',
  eval_or_match true es fuel st env uu uu = (fin_st, Rval vs) ->
  eval_or_match true es' fuel' st' env' uu uu = (fin_st', Rval vs') ->
  exists both_fuel,
  eval_or_match true es both_fuel st env uu uu = (fin_st, Rval vs) /\
  eval_or_match true es' both_fuel st' env' uu uu = (fin_st', Rval vs').
Proof.
  intros.
  destruct (Compare_dec.lt_eq_lt_dec fuel fuel') as [[n_lt_m | n_eq_m] | m_lt_n].
  - exists fuel'; split.
    apply more_fuel_same_result with fuel.
    lia.
    discriminate.
    assumption.
    assumption.
  - exists fuel'; split; subst; assumption.
  - exists fuel; split.
    assumption.
    apply more_fuel_same_result with fuel'.
    lia.
    discriminate.
    assumption.
Qed.

Theorem EVAL_EApp_Opapp {A B : Type} (env : sem_env val) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop)
  (f : A -> B) (a : A) (cl v : exp) :
  EVAL env cl (FUNC AINV BINV f) ->
  EVAL env v (AINV a) ->
  EVAL env (EApp Opapp [cl;v]) (BINV (f a)).
Proof.
  unfold EVAL, evaluate.
  intros HEVAL_cl HEVAL_v st.
  specialize (HEVAL_v st).
  destruct HEVAL_v as [v_v [fuel' [st_v [Heval_v HFUNC_a_v_v]]]].
  specialize (HEVAL_cl st_v).
  destruct HEVAL_cl as [v_cl [fuel [st_cl [Heval_cl HFUNC_f_v_cl]]]].
  specialize (HFUNC_f_v_cl a v_v HFUNC_a_v_v).
  destruct HFUNC_f_v_cl as [cl_v [HBINV_fa_cl_v Happ_ret_v_cl]].
  unfold app_returns in Happ_ret_v_cl.
  specialize (Happ_ret_v_cl v_v HFUNC_a_v_v st_cl).
  destruct Happ_ret_v_cl as [env' [exp0 [st_final [v_final [Hdo_app [Heval_rel HBINV_fa_v_final]]]]]].
  unfold eval_rel in Heval_rel.
  destruct Heval_rel as [fuel'' Hevaluate].
  exists v_final.
  apply (use_maximum_fuel [fuel; fuel'; fuel'']) in Heval_cl.
  apply (use_maximum_fuel [fuel; fuel'; fuel'']) in Hevaluate.
  apply (use_maximum_fuel [fuel; fuel'; fuel'']) in Heval_v.
  remember (list_max [fuel; fuel'; fuel'']) as the_fuel.
  exists (S the_fuel).
  exists st_final.
  split.
  simp eval_or_match; simpl.
  simp eval_or_match; simpl.
  rewrite Heval_v; simpl.
  rewrite Heval_cl; simpl.
  Opaque list_max.
  break_match; try inv Hdo_app; simpl.
  rewrite Hevaluate.
  reflexivity.
  simpl.
  rewrite H0.
  simpl.
  rewrite Hevaluate.
  reflexivity.
  assumption.
  apply in_max_le.
  right.
  constructor; reflexivity.
  apply in_max_le.
  right. right. constructor. reflexivity.
  apply in_max_le. constructor. reflexivity.
Qed.

Theorem EVAL_EVar : forall (A : Type) (a : A) (AINV : A -> val -> Prop) env varname v,
    nsLookup ident_string_beq varname (sev env) = Some v ->
    AINV a v ->
    EVAL env (EVar varname) (AINV a).
Proof.
  unfold EVAL.
  unfold evaluate.
  intros A a AINV env varname v Hlookup HAINVa st.
  exists v, 0, st.
  simp eval_or_match.
  rewrite Hlookup; simpl.
  split; try assumption; try reflexivity.
Qed.

Theorem EVAL_EVar_Recclosure_alt : forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) n f env cl_env,
   forall funs fname name body,
      NoDup (List.map (fun '(f,x,e) => f) funs) ->
      (forall v, AINV n v ->
            EVAL (bind_variable_name name v (update_sev cl_env (build_rec_env funs cl_env (sev cl_env)))) body (BINV (f n))) ->
      nsLookup ident_string_beq (Short fname) (sev env) = Some (Recclosure cl_env funs fname) ->
      (find_recfun fname funs = Some (name,body)) ->
      EVAL env (EVar (Short fname)) ((FUNC (EQ AINV n) BINV) f).
Proof.
  unfold EVAL, evaluate.
  intros A B AINV BINV n f env cl_env funs fname name body HNoDup HEVALbody Hlookupfname Hfindfname st.
  eexists.
  exists 0. eexists.
  split.
  simp eval_or_match; simpl.
  rewrite Hlookupfname.
  reflexivity.
  unfold FUNC.
  unfold EQ.
  unfold app_returns.
  intros x v [Hneqx HAINVx].
  subst.
  destruct (HEVALbody v HAINVx st) as [v' [f' [st' [HEVALbody' HBINVfx]]]].
  exists v'.
  split; try assumption.
  intros v0 [_ HAINVx'] st0.
  destruct (HEVALbody v0 HAINVx' st0) as [v0' [f0' [st0' [HEVALbody0' HBINVfxv0]]]].
  do 4 eexists.
  split.
  simpl.
  break_match.
  rewrite Hfindfname.
  reflexivity.
  contradiction.
  unfold eval_rel.
  split.
  eexists.
  unfold evaluate.
  unfold bind_variable_name in HEVALbody0'.
  unfold update_sev in *; simpl in *.
  apply HEVALbody0'.
  assumption.
Qed.

Theorem Eval_EVar_Recclosure : forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop)
                            f fname name body n env cl_env,
   (forall v, AINV n v ->
         EVAL (bind_variable_name name v
                 (update_sev cl_env (build_rec_env [(fname,name,body)] cl_env (sev cl_env))))
              body (BINV (f n))) ->
    nsLookup ident_string_beq (Short fname) (sev env) = Some (Recclosure cl_env [(fname,name,body)] fname) ->
    EVAL env (EVar (Short fname)) ((FUNC (EQ AINV n) BINV) f).
Proof.
  unfold EVAL, evaluate.
  intros A B AINV BINV f fname name body n env cl_env Hbody Hlookup st.
  do 3 eexists.
  split.
  - simp eval_or_match; simpl.
    rewrite Hlookup; simpl.
    reflexivity.
  - unfold FUNC.
    unfold EQ.
    intros x v [Hneqx HAINVxv].
    subst.
    destruct (Hbody v HAINVxv st) as [v' [f' [st' [Hbody' HBINVfxv']]]].
    exists v'.
    split; try assumption.
    unfold app_returns.
    intros v0 [Heqx HAINVxv0] st0.
    destruct (Hbody v0 HAINVxv0 st0) as [v0' [f0' [st0' [Hbody0' HBINVfxv0']]]].
    do 4 eexists.
    split; try reflexivity.
    simpl.
    destruct string_dec.
    reflexivity.
    contradiction.
    unfold eval_rel.
    split.
    eexists.
    unfold evaluate.
    unfold bind_variable_name, update_sev in *; simpl in *.
    rewrite Hbody0'.
    reflexivity.
    assumption.
    Unshelve.
    constructor.
Qed.

Theorem EVAL_ELetrec :
  forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) f fname env n var body,
    (forall v, AINV n v ->
          EVAL (bind_variable_name var v
                  (update_sev env (build_rec_env [(fname,var,body)] env (sev env))))
            body (BINV (f n))) ->
    EVAL env (ELetrec [(fname,var,body)] (EVar (Short fname))) ((FUNC (EQ AINV n) BINV) f).
Proof.
  unfold EVAL, evaluate.
  intros A B AINV BINV f fname env n var body Henv_update st.
  do 3 eexists.
  simp eval_or_match; simpl.
  split.
  - break_match.
    + unfold nsLookup.
      simpl.
      rewrite eqb_refl; simpl.
      reflexivity.
    + assert (NoDup [fname]).
      constructor.
      intro contra.
      contradiction.
      constructor.
      contradiction.
  - unfold FUNC, EQ.
    intros x v H.
    destruct H as [Hneqx HAINVv]; subst.
    destruct (Henv_update v HAINVv st) as [v0 [f0 [st0 [Hevalbody HBINVv0]]]].
    exists v0.
    split; try assumption.
    unfold app_returns.
    intros v1 [Hxeqx HAINVv1] st0'.
    destruct (Henv_update v1 HAINVv1 st0') as [v' [f' [st' [Hevalbody' HBINVv1]]]].
    do 4 eexists.
    split.
    simpl.
    destruct (string_dec fname fname); try reflexivity; try contradiction.
    unfold eval_rel.
    split; try assumption.
    eexists.
    unfold evaluate.
    unfold bind_variable_name in Hevalbody'.
    unfold update_sev in *; simpl in *.
    apply Hevalbody'.
    assumption.
    Unshelve.
    constructor.
Qed.

(* Utilities for Coq provided types or general logic *)

Lemma forall_push_conj : forall (A : Type) (P : Prop) (Q : A -> Prop), inhabited A -> P /\ (forall x, Q x) <->  forall (x : A), P /\ Q x.
Proof.
  intros.
  split.
  - intros [HP HQ] x.
    split; auto.
  - intros.
    destruct H.
    destruct (H0 X).
    split; auto.
    intro x.
    destruct (H0 x); auto.
Qed.

Theorem Forall2_app_entail_R : forall (A B : Type) (R : A -> B -> Prop) x y l1 l2,  Forall2 R (l1 ++ [x]) (l2 ++ [y]) -> R x y.
Proof.
  intros A B R x y l1.
  induction l1; intros l2 H.
  inv H.
  inv H4.
  destruct l2.
  inv H.
  assumption.
  inv H.
  destruct l2; inv H8.
  destruct l2.
  inv H. inv H5.
  destruct l1; inv H1.
  inv H.
  eapply IHl1.
  apply H5.
Qed.

Theorem Forall2_app_smaller : forall (A B : Type) (R : A -> B -> Prop) x y l1 l2, Forall2 R (l1 ++ [x]) (l2 ++ [y]) -> Forall2 R l1 l2.
Proof.
  intros A B R x y l1.
  induction l1; intros l2 H.
  inv H.
  inv H4.
  destruct l2; inv H2.
  constructor.
  destruct l2; inv H2.
  destruct l2.
  inv H.
  inv H5.
  destruct l1; inv H1.
  inv H.
  constructor.
  assumption.
  apply IHl1.
  assumption.
Qed.

Theorem Forall2_rev : forall (A B : Type) (R : A -> B -> Prop) l1 l2,  Forall2 R l1 l2 <-> Forall2 R (rev l1) (rev l2).
  intros A B R l1.
  induction l1; intro l2; split; intro H.
  - inv H.
    constructor.
  - inv H.
    destruct l2.
    constructor.
    simpl in H0. destruct (rev l2); inv H0.
  - inv H.
    simpl in *.
    assert (H' : Forall2 R [a] [y]) by (constructor; try assumption; try constructor).
    apply Forall2_app.
    apply IHl1.
    assumption.
    assumption.
  - destruct l2. inv H.
    destruct (rev l1); inv H1.
    simpl in *.
    constructor.
    eapply Forall2_app_entail_R.
    apply H.
    rewrite IHl1.
    eapply Forall2_app_smaller.
    apply H.
Qed.

Theorem Forall2_rev_swap : forall (A B : Type) (R : A -> B -> Prop) l1 l2,  Forall2 R l1 (rev l2) <-> Forall2 R (rev l1) (l2).
Proof.
  intros A B R l1 l2.
  assert (Hl1 : l1 = rev (rev l1)) by (rewrite rev_involutive; reflexivity).
  assert (Hl2 : l2 = rev (rev l2)) by (rewrite rev_involutive; reflexivity).
  split; intro H.
  - rewrite Hl2.
    rewrite <- Forall2_rev.
    assumption.
  - rewrite Hl1.
    rewrite <- Forall2_rev.
    assumption.
Qed.

(* end of that little section *)

Lemma EVAL_inv_split : forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) f env e,
    inhabited A ->
    (forall x, EVAL env e ((FUNC (EQ AINV x) BINV) f)) ->
    forall st, exists v f' st', evaluate [e] f' st env = (st', Rval [v]) /\ forall x, (FUNC (EQ AINV x) BINV f) v.
Proof.
  unfold EVAL.
  intros.
  destruct H.
  destruct (H0 X st) as [v [fuel [st' [Heval HFUNC]]]].
  exists v, fuel, st'.
  split.
  - assumption.
  - intros. destruct (H0 x st) as [v' [fuel' [st'' [Heval' Hother]]]].
    apply (use_maximum_fuel [fuel; fuel']) in Heval.
    apply (use_maximum_fuel [fuel; fuel']) in Heval'.
    Opaque list_max.
    rewrite Heval in Heval'.
    inv Heval'.
    assumption.
    apply in_max_le. right. constructor. reflexivity.
    apply in_max_le. constructor. reflexivity.
Qed.

Theorem EVAL_remove_EQ : forall (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) f env e,
    inhabited A -> (forall x, EVAL env e ((FUNC (EQ AINV x) BINV) f)) -> EVAL env e ((FUNC AINV BINV) f).
Proof.
  intros A B AINV BINV f env e Hi H st.
  specialize (EVAL_inv_split A B AINV BINV f env e Hi H st).
  intro.
  destruct H0 as [v [fuel [st' [Heval HFUNC]]]].
  do 3 eexists.
  split.
  - apply Heval.
  - unfold FUNC in HFUNC. unfold FUNC.
    intros.
    rewrite <- exists_EQ_INV_iff_INV in H0.
    destruct H0.
    specialize (HFUNC x0 x v0 H0).
    destruct HFUNC as [u [HBINVu Happ_ret]].
    eexists.
    split.
    + apply HBINVu.
    + unfold app_returns in *.
      intros.
      inv H0. clear H0.
      apply Happ_ret.
      unfold EQ.
      split; auto.
Qed.

Lemma EVAL_Forall_eval_or_match_has_value : forall ps env st,
    Forall (fun '(P, x) => EVAL env x P) ps ->
    exists vs st' f, eval_or_match true (rev (map snd ps)) f st env uu uu = (st', Rval vs).
  intros ps0 env1 st1 Hassert.
  generalize dependent st1.
  induction ps0; intro st1.
  + exists [], st1, 0.
    simp eval_or_match.
    reflexivity.
  + inv Hassert. clear Hassert.
    destruct a.
    specialize (IHps0 H2 st1).
    destruct IHps0 as [vs [st' [f Hevalps0]]].
    specialize (H1 st').
    destruct H1 as [v [f' [st'0 [Heval HP]]]].
    destruct (Compare_dec.lt_eq_lt_dec f f') as [[f_lt_f' | f_eq_f'] | f_gt_f']; do 3 eexists.
  - simp eval_or_match; simpl.
    rewrite eval_or_match_app.
    apply (more_fuel_same_value f f') in Hevalps0.
    unfold evaluate in Hevalps0.
    rewrite Hevalps0.
    unfold evaluate in Heval.
    rewrite Heval.
    reflexivity.
    lia.
  - simp eval_or_match; simpl.
    rewrite eval_or_match_app.
    subst.
    rewrite Hevalps0.
    unfold evaluate in Heval.
    rewrite Heval.
    reflexivity.
  - simp eval_or_match; simpl.
    rewrite eval_or_match_app.
    apply (more_fuel_same_value f' f) in Heval.
    unfold evaluate in Hevalps0.
    rewrite Hevalps0.
    unfold evaluate in Heval.
    rewrite Heval.
    reflexivity.
    lia.
Qed.

Lemma EVAL_ECon_lemma : forall ps st env,
    (forall P e, In (P,e) ps -> EVAL env e P) ->
      exists f st' vals , evaluate (map snd ps) f st env = (st' ,Rval vals) /\
                       Forall2 (fun '(P,_) v => P v) ps vals.
Proof.
  intros ps st env H.
  assert (H' : forall Pe, In (Pe) ps -> (fun '(P,e) => EVAL env e P) Pe) by (destruct Pe; apply H).
  clear H.
  rewrite <- Forall_forall in H'.
  unfold EVAL, evaluate in *.
  generalize dependent st.
  induction H'; intros st.
  - do 3 eexists.
    split.
    simp eval_or_match.
    reflexivity.
    constructor.
  - destruct x.
    specialize (H st).
    destruct H as [v [f [st' [Hevale HP]]]].
    specialize (IHH' st').
    destruct IHH' as [f' [st'' [vals [Hevall HForall2]]]].
    destruct (Compare_dec.lt_eq_lt_dec f f') as [[f_lt_f' | f_eq_f'] | f_gt_f']; do 3 eexists; split.
    + simpl.
      rewrite eval_or_match_cons.
      apply (more_fuel_same_value f f') in Hevale; unfold evaluate in *; try lia.
      rewrite Hevale.
      rewrite Hevall.
      reflexivity.
    + constructor.
      assumption.
      assumption.
    + simpl. subst.
      rewrite eval_or_match_cons.
      rewrite Hevale.
      rewrite Hevall.
      reflexivity.
    + constructor.
      assumption.
      assumption.
    + simpl.
      rewrite eval_or_match_cons.
      apply (more_fuel_same_value f' f) in Hevall; unfold evaluate in *; try lia.
      rewrite Hevale.
      rewrite Hevall.
      reflexivity.
    + constructor; assumption.
      Unshelve.
      constructor.
Qed.

Theorem EVAL_ECon :
  forall (Q : val -> Prop) es (ps : list ((val -> Prop) * exp)) stmp name env,
    (map snd ps) = es ->
    nsLookup ident_string_beq name (sec env) = Some (length ps, stmp) ->
    Forall (fun '(P,x) => EVAL env x P) ps ->
    (forall vals,
        Forall2 (fun '(P,_) v => P v) ps vals -> Q (Conv (Some stmp) vals)) ->
    EVAL env (ECon (Some name) es) Q.
Proof.
  intros Q es ps stmp name env sub Hlookup HForall HForall2.
  subst.
  intros st. unfold evaluate.
  specialize (EVAL_Forall_eval_or_match_has_value ps env st HForall).
  intro Hthing.
  destruct Hthing as [vs [st' [f' Hevalval]]].
  do 3 eexists.
  simp eval_or_match; simpl.
  rewrite Hlookup; simpl.
  rewrite map_length.
  rewrite PeanoNat.Nat.eqb_refl; simpl.
  rewrite Hevalval; simpl.
  unfold ident_string_beq in Hlookup.
  rewrite Hlookup; simpl.
  split.
  reflexivity.
  apply HForall2.
  rewrite Forall_forall in HForall.
  assert (Hlem : forall P e, In (P,e) ps -> EVAL env e P).
  {
    intros.
    specialize (HForall (P,e)).
    apply HForall. assumption.
  }
  assert  (H : exists f st' vals , evaluate (map snd (rev ps)) f st env = (st' ,Rval vals) /\
                       Forall2 (fun '(P,_) v => P v) (rev ps) vals) by
    (apply EVAL_ECon_lemma; intros; apply Hlem; rewrite in_rev; assumption).
  destruct H as [f'' [st'' [vals [Hevalvals HForall2vals]]]].
  rewrite Forall2_rev_swap.
  assert (H' : map snd (rev ps) = rev (map snd ps)) by (rewrite map_rev; reflexivity).
  rewrite H' in Hevalvals; clear H'.
  destruct (Compare_dec.lt_eq_lt_dec f' f'') as [[f'_lt_f'' | f'_eq_f''] | f'_gt_f''].
  - apply (more_fuel_same_value f' f'') in Hevalval; try lia;
      rewrite Hevalval in Hevalvals; inv Hevalvals; assumption.
  - subst. unfold evaluate in *. rewrite Hevalval in Hevalvals; inv Hevalvals; assumption.
  - apply (more_fuel_same_value f'' f') in Hevalvals; try lia; unfold evaluate in *;
      rewrite Hevalval in Hevalvals; inv Hevalvals; assumption.
Qed.