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

Require Import RefineInv.

(* example invariants that should be generatable *)
Fixpoint LIST {A : Type} (a_inv : A -> val -> Prop) (l : list A) (v : val) : Prop :=
  match l return Prop with
  | [] => v = Conv (Some (TypeStamp "Nil" O)) []
  | a::t => exists (v1 v2 : val), v = Conv (Some (TypeStamp "Cons" O)) [v1;v2]
                           /\ a_inv a v1 /\ LIST a_inv t v2
  end.

Definition BOOL (b : bool) (v : val) : Prop :=
  match b with
  | true => v = Conv (Some (TypeStamp "True" O)) []
  | false => v = Conv (Some (TypeStamp "False" O)) []
  end.

Definition good_cons_env (pes : list (pat * exp)) (env : sem_env val) (consty : stamp):=
  Forall (fun '(p,e) => exists con_name ps ty,
              p = Pcon (Some con_name) ps /\
                NoDup (pat_bindings p []) /\
                nsLookup ident_string_beq con_name (sec env) = Some (length ps, TypeStamp (id_to_n con_name) ty) /\
                stamp_same_type (TypeStamp (id_to_n con_name) ty) consty = true) pes.


Theorem simple_list_cases_inv : forall (A B : Type) (a_inv : A -> val -> Prop ) (b_inv : B -> val -> Prop) (mat c1 c2 : exp) (b1 : B) (b2 : A -> list A -> B) (l : list A) (orig : B) a_str l'_str env,
  (* Hate this *)
  orig = match l with [] => b1 | x::xs => b2 x xs end ->
  (* needs some way to ensure the environment contains the correct types *)
  good_cons_env [(Pcon (Some (Short "Nil")) [], c1);
                 (Pcon (Some (Short "Cons")) [Pvar a_str; Pvar l'_str], c2)]
                env (TypeStamp "" 0) ->
  (* Wierdness from generalization *)
  a_str <> l'_str ->
  (* list inv holds for list we are matching on *)
  EVAL env mat (LIST a_inv l) ->
  (* b inv holds for the first body of the match  *)
  (l = [] -> EVAL env c1 (b_inv b1)) ->
  (* for any given x : A and xs : list A, if the a inv holds for x for some v and the *)
  (* list inv holds for xs for some vs, then b inv holds for the second body of the match *)
  (* applied to x and xs  *)
  (forall (x : A) (xs : list A) (v vs : val),
      l = x::xs ->
      a_inv x v /\ (LIST a_inv xs vs) ->
      EVAL
        (extend_dec_env (Build_sem_env (nsBind l'_str vs (nsBind a_str v nsEmpty)) nsEmpty) env)
        c2 (b_inv (b2 x xs))) ->

      EVAL env (EMat mat [(Pcon (Some (Short "Nil")) [], c1);
                          (Pcon (Some (Short "Cons")) [Pvar a_str; Pvar l'_str], c2)])
                          (b_inv orig).
Proof.
  unfold EVAL; simpl.
  unfold evaluate; simpl.
  unfold good_cons_env; simpl.
  intros A B a_inv b_inv mat c1 c2 b1 b2 l orig a_str l'_str env any Hgoodcons Ha_neq_l_str H_match H_clause1 H_clause2 st.
  inv Hgoodcons.
  inv H2.
  destruct H1 as [Nilname [ps [ty [Heq [HNoDup [Hlookup Htypeeq]]]]]].
  destruct H3 as [Consname [ps_cons [ty_cons [Heq' [HNoDupcons [Hlookup_cons Htype_eq_cons]]]]]].
  inv Heq; clear Heq.
  inv Heq'; clear Heq'.
  unfold extend_dec_env in H_clause2.
  simpl in H_clause2.
  destruct l as [| a' as' ].
  - subst.
    specialize (H_match st).
    destruct H_match as [v_mat H_match].
    destruct H_match as [f_mat H_match].
    destruct H_match as [st_mat H_match].
    destruct H_match as [H_match list_inv_mat].
    specialize (H_clause1 eq_refl st_mat).
    destruct H_clause1 as [v_c1 H_clause1].
    destruct H_clause1 as [f_c1 H_clause1].
    destruct H_clause1 as [st_c1 H_clause1].
    destruct H_clause1 as [H_clause1 b_inv_c1].
    destruct (Compare_dec.lt_eq_lt_dec f_c1 f_mat) as [ [c1_lt_mat | c1_eq_mat] | mat_lt_c1 ]; do 3 eexists; split; simpl in *; subst.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq.
      subst; simpl.
      rewrite <- sem_env_id.
      eapply more_fuel_same_value.
      apply c1_lt_mat.
      eapply eval_or_match_inc_fuel_res.
      discriminate.
      rewrite H_clause1.
      reflexivity.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      rewrite <- sem_env_id.
      rewrite H_clause1.
      reflexivity.
      lia.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      rewrite <- sem_env_id.
      rewrite H_clause1.
      reflexivity.
      lia.
    + assumption.
  - specialize (H_match st).
    destruct H_match as [v_mat H_match].
    destruct H_match as [f_mat H_match].
    destruct H_match as [st_mat H_match].
    destruct H_match as [H_match list_inv_mat].
    destruct list_inv_mat as [v1 list_inv_mat].
    destruct list_inv_mat as [v2 list_inv_mat].
    destruct list_inv_mat as [v_mat_sub list_inv_l].
    destruct list_inv_l as [a_inv_v1 list_inv_v2].
    assert (a_inv a' v1 /\ LIST a_inv as' v2) as list_inv_hyp by (split; assumption).
    specialize (H_clause2 a' as' v1 v2 eq_refl list_inv_hyp st_mat).
    destruct H_clause2 as [v_c2 H_clause2].
    destruct H_clause2 as [f_c2 H_clause2].
    destruct H_clause2 as [st_c2 H_clause2].
    destruct H_clause2 as [H_clause2 b_inv_c2].
    destruct (Compare_dec.lt_eq_lt_dec f_c2 f_mat) as [ [c2_lt_mat | c2_eq_mat] | mat_lt_c2 ];
    do 3 eexists; split; simpl in *; subst.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      (* new *)
      break_match; simpl.
      (* end new*)
      * rewrite Hlookup_cons; simpl.
        rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
        simp pmatch; simpl.
        eapply more_fuel_same_value.
        apply c2_lt_mat.
        eapply eval_or_match_inc_fuel_res.
        discriminate.
        apply H_clause2.
      * assert (NoDup [l'_str; a_str]).
        { constructor.
          intro contra.
          inv contra.
          contradiction.
          inv H.
          constructor.
          intro contra.
          inv contra.
          constructor. }
        contradiction.
    + simp eval_or_match; simpl.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup_cons; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      break_match; simpl.
      * apply H_clause2.
      * assert (NoDup [l'_str; a_str]).
        { constructor.
          intro contra.
          inv contra.
          contradiction.
          inv H.
          constructor.
          intro contra.
          inv contra.
          constructor. }
        contradiction.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      destruct (string_dec a_str l'_str); try contradiction.
      rewrite Hlookup_cons; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
      simp pmatch; simpl.
      lia.
    + assumption.
Qed.

Fixpoint NAT (n : nat) (v : val) :=
  match n with
  | O => v = Conv (Some (TypeStamp "O" 0)) []
  | S n' => exists v', v = Conv (Some (TypeStamp "S" 0)) [v'] /\ NAT n' v'
  end.

Definition length_inv (A : Type) (a_inv : A -> val -> Prop) :=
  FUNC (LIST a_inv) NAT (@length _).

Definition length_exp := (ELetrec
      [("length", "l",
        EMat (EVar (Short "l"))
          [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "O")) []);
           (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "l'"],
            ECon (Some (Short "S"))
              [EApp Opapp [EVar (Short "length"); EVar (Short "l'")]])])]
      (EVar (Short "length"))).

Definition length_env : sem_env val := {|
            sev := [];
            sec := [(Short "Cons", (2, TypeStamp "Cons" 0)); (Short "Nil", (0, TypeStamp "Nil" 0)); (Short "O", (0, TypeStamp "O" 0)); (Short "S", (1, TypeStamp "S" 0))]
          |}.

Ltac In_solve := match goal with
                  | |- ~ In ?i [] => auto
                  | |- ~ In ?i ?l => intros [contra | rest]; [inv contra | In_solve]
                  | H : In ?i ?l |- False => inv H
                  | _ => simpl
                  end.

Ltac NoDup_solve := simpl; match goal with
                           | |- NoDup [] => constructor
                           | |- NoDup (?x::?xs) => constructor; [try In_solve | try NoDup_solve]
                           end.

Ltac good_cons_env_solve := unfold good_cons_env;
                            match goal with
                            | |- Forall ?P [] => constructor
                            | |- Forall ?P (?x::?xs) => constructor;
                                                      [do 3 eexists; split;
                                                       [ reflexivity | split;
                                                       [ NoDup_solve | split;
                                                       [ reflexivity |
                                                         reflexivity ]]] |
                                                        good_cons_env_solve]
                            end.

Theorem length_final_exp :
  forall A a_inv l,
    EVAL length_env
      (ELetrec
         [("length", "l",
            EMat (EVar (Short "l"))
              [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "O")) []);
               (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "l'"],
                 ECon (Some (Short "S")) [EApp Opapp [EVar (Short "length"); EVar (Short "l'")]])])]
         (EVar (Short "length")))
      ((FUNC (EQ (LIST a_inv) l) NAT) (@length A)).
Proof.
  intros A AINV l.
  induction l; apply EVAL_ELetrec; intros v HLISTl; inv HLISTl.
  - apply (simple_list_cases_inv A nat AINV NAT _ _ _ 0 (fun _ l' => S (length l')) []).
    + reflexivity.
    + good_cons_env_solve.
    + discriminate.
    + eapply EVAL_EVar.
      * unfold nsLookup.
        simpl.
        reflexivity.
      * assumption.
    + intro. apply EVAL_ECon with [] (TypeStamp "O" 0).
      * reflexivity.
      * unfold nsLookup. reflexivity.
      * constructor.
      * intros. inv H0. reflexivity.
    + intros. inv H.
  - apply (simple_list_cases_inv A nat AINV NAT _ _ _ 0 (fun _ l' => S (length l')) (a::l)).
    + reflexivity.
    + good_cons_env_solve.
    + discriminate.
    + eapply EVAL_EVar.
      * unfold nsLookup.
        simpl.
        reflexivity.
      * assumption.
    + intro. inv H0.
    + intros. inv H0; clear H0. inv H1; clear H1.
      apply EVAL_ECon with
        [(NAT (length xs), EApp Opapp [EVar (Short "length"); EVar (Short "l'")])]
        (TypeStamp "S" 0).
      * reflexivity.
      * unfold nsLookup; reflexivity.
      * constructor.
        -- apply app_evaluates_to with (EQ (LIST AINV) xs).
           ++ generalize dependent IHl.
              unfold EVAL, evaluate.
              intros IHl.
              intro.
              specialize (IHl st).
              destruct IHl as [vl [fl [stl [IHeval IHFUNC]]]].
              do 3 eexists.
              simp eval_or_match in *; simpl in *.
              split.
              reflexivity.
              break_match.
              inv IHeval.
              assumption.
              inv IHeval.
           ++ apply EVAL_EQ.
              unfold EVAL, evaluate.
              intro st.
              do 3 eexists.
              split.
              unfold extend_dec_env. unfold nsAppend. simpl.
              simp eval_or_match.
              unfold nsLookup. simpl.
              reflexivity.
              apply H2.
        -- constructor.
      * intros.
        destruct H.
        destruct H.
        destruct H3.
        simpl.
        inv H1.
        inv H9.
        exists y.
        split; try reflexivity; try assumption.
        Unshelve.
        constructor.
        constructor.
Qed.

Theorem length_final_exp_no_EQ :
  forall A a_inv,
    EVAL length_env
      (ELetrec
         [("length", "l",
            EMat (EVar (Short "l"))
              [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "O")) []);
               (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "l'"],
                 ECon (Some (Short "S")) [EApp Opapp [EVar (Short "length"); EVar (Short "l'")]])])]
         (EVar (Short "length")))
      ((FUNC (LIST a_inv) NAT) (@length A)).
Proof.
  intros A AINV Hinhab.
  apply EVAL_remove_EQ.
  - constructor. constructor.
  - intros. apply length_final_exp.
Qed.

Definition DECL (st : state ST) (env : sem_env val) (decs : list dec) (st' : state ST) (env' : sem_env val) : Prop := exists f, evaluate_decs f st env decs = (st', Rval env').

Theorem DECL_nil : forall st env, DECL st env [] st empty_sem_env.
Proof.
  intros.
  exists 0.
  simp evaluate_decs.
  reflexivity.
Qed.

Theorem evaluate_decs_inc_fuel : forall (f : nat) (st st' : state ST) (env env' : sem_env val)
                                     (ds : list dec),
    evaluate_decs f st env ds = (st', Rval env') -> evaluate_decs (S f) st env ds = (st', Rval env').
Proof.
  intros.
  funelim (evaluate_decs f st env ds); simp evaluate_decs in *.
  - break_match.
    + remember (evaluate [e] fuel st env). destruct p0. destruct r.
      symmetry in Heqp0.
      apply (more_fuel_same_value fuel (S fuel)) in Heqp0; try lia.
      rewrite Heqp0.
      assumption.
      inv Heqp0.
      inv H.
    + inv H.
  - remember (evaluate_decs fuel st env ds). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    assumption.
    inv H0.
  - remember (evaluate_decs fuel st env ds1). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    eapply H0; try constructor.
    constructor.
    constructor.
    constructor.
    assumption.
    inv H1.
  - clear Heqcall.
    remember (evaluate_decs fuel st env [d1]). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    remember (evaluate_decs fuel s (extend_dec_env s0 env) (d2 :: decl')). destruct p.
    destruct r.

    assert (copyHeqp0 : (s1, Rval s2) = evaluate_decs fuel s (extend_dec_env s0 env) (d2 :: decl')) by assumption.
    rewrite Heqp0 in Heqp0.
    eapply H0 in Heqp0.
    rewrite Heqp0.
    inv H1.
    apply H1.
    constructor.
    constructor.
    constructor.
    constructor.
    symmetry. assumption.
    reflexivity.
    inv H1.
    inv H1.
Qed.

Theorem evaluate_decs_more_fuel_same_value : forall (f f' : nat) (st st' : state ST) (env env' : sem_env val)
                                     (ds : list dec),
   f <= f' -> evaluate_decs f st env ds = (st', Rval env') -> evaluate_decs f' st env ds = (st', Rval env').
Proof.
  intros.
  induction H.
  assumption.
  apply evaluate_decs_inc_fuel.
  assumption.
Qed.

Theorem DECL_Dlet : forall (AINV : val -> Prop) st env locs name e,
    EVAL env e AINV ->
    exists v st', DECL st env [Dlet locs (Pvar name) e] st' {| sec := nsEmpty; sev := alist_to_ns [(name, v)] |}.
Proof.
  unfold EVAL, DECL.
  intros.
  destruct (H st) as [v [f [ste [Heval HAINVv]]]].
  exists v, ste, f.
  simp evaluate_decs.
  simpl.
  rewrite Heval.
  simp pmatch.
  simpl.
  reflexivity.
Qed.

Theorem DECL_Dletrec : forall env fname varname body st locs,
    DECL st env [Dletrec locs [(fname,varname,body)]] st
         {| sec := nsEmpty; sev := alist_to_ns [(fname, (Recclosure env [(fname,varname,body)] fname))] |}.
Proof.
  unfold EVAL, DECL.
  intros.
  exists 0.
  simp evaluate_decs; simpl.
  unfold build_rec_env, nsBind.
  reflexivity.
Qed.

Theorem DECL_Dtype : forall tyvars tyname constrs st env locs,
  NoDup (map fst constrs) ->
  DECL st env [Dtype locs [(tyvars, tyname, constrs)]] (state_update_next_type_stamp st (next_type_stamp st + 1))
                {| sec := build_tdefs (next_type_stamp st) [(tyvars, tyname, constrs)] ; sev := nsEmpty |}.
Proof.
  unfold DECL.
  intros.
  exists 0.
  simp evaluate_decs; simpl.
  break_match.
  - reflexivity.
  - assert (contra :  Forall UniqueCtorsInDef [(tyvars, tyname, constrs)]) by
      (constructor; try assumption; try constructor).
    contradiction.
Qed.

Theorem DECL_cons : forall st env d ds st' st'' env' env'',
    DECL st env [d] st' env' ->
    DECL st' (extend_dec_env env' env) ds st'' env'' ->
    DECL st env (d::ds) st'' (extend_dec_env env'' env').
Proof.
  unfold DECL.
  intros.
  destruct H.
  destruct H0.
  destruct (Compare_dec.lt_eq_lt_dec x x0) as [[f_1_lt_0 | f_1_eq_0] | f_1_gt_0]; eexists.
  - apply (evaluate_decs_more_fuel_same_value x x0) in H; try lia.
    rewrite evaluate_decs_cons.
    rewrite H.
    rewrite H0.
    unfold combine_dec_result.
    reflexivity.
  - subst.
    rewrite evaluate_decs_cons.
    rewrite H.
    rewrite H0.
    unfold combine_dec_result.
    reflexivity.
  - apply (evaluate_decs_more_fuel_same_value x0 x) in H0; try lia.
    rewrite evaluate_decs_cons.
    rewrite H.
    rewrite H0.
    unfold combine_dec_result.
    reflexivity.
Qed.


(* Full Map example *)

(* GenerateInv list. *)
Definition list_INV := fun (A : Type) (A_INV : A -> val -> Prop) =>
                       fix list_INV (l : list A) (v : val) : Prop :=
    match l with
    | [] => v = Conv (Some (TypeStamp "Nil" O)) []
    | a::t => exists (v1 v2 : val), v = Conv (Some (TypeStamp "Cons" O)) [v1;v2]
                             /\ A_INV a v1 /\ list_INV t v2
    end.

Theorem simple_list_cases_inv' : forall (A B : Type) (a_inv : A -> val -> Prop ) (b_inv : B -> val -> Prop) (mat c1 c2 : exp) (b1 : B) (b2 : A -> list A -> B) (l : list A) (orig : B) a_str l'_str env,
  (* Hate this *)
  orig = match l with [] => b1 | x::xs => b2 x xs end ->
  (* needs some way to ensure the environment contains the correct types *)
  good_cons_env [(Pcon (Some (Short "Nil")) [], c1);
                 (Pcon (Some (Short "Cons")) [Pvar a_str; Pvar l'_str], c2)]
                env (TypeStamp "" 0) ->
  (* Wierdness from generalization *)
  a_str <> l'_str ->
  (* list inv holds for list we are matching on *)
  EVAL env mat (list_INV A a_inv l) ->
  (* b inv holds for the first body of the match  *)
  (l = [] -> EVAL env c1 (b_inv b1)) ->
  (* for any given x : A and xs : list A, if the a inv holds for x for some v and the *)
  (* list inv holds for xs for some vs, then b inv holds for the second body of the match *)
  (* applied to x and xs  *)
  (forall (x : A) (xs : list A) (v vs : val),
      l = x::xs ->
      a_inv x v /\ (list_INV A a_inv xs vs) ->
      EVAL
        (extend_dec_env (Build_sem_env (nsBind l'_str vs (nsBind a_str v nsEmpty)) nsEmpty) env)
        c2 (b_inv (b2 x xs))) ->

      EVAL env (EMat mat [(Pcon (Some (Short "Nil")) [], c1);
                          (Pcon (Some (Short "Cons")) [Pvar a_str; Pvar l'_str], c2)])
                          (b_inv orig).
Proof.
  unfold EVAL; simpl.
  unfold evaluate; simpl.
  unfold good_cons_env; simpl.
  intros A B a_inv b_inv mat c1 c2 b1 b2 l orig a_str l'_str env any Hgoodcons Ha_neq_l_str H_match H_clause1 H_clause2 st.
  inv Hgoodcons.
  inv H2.
  destruct H1 as [Nilname [ps [ty [Heq [HNoDup [Hlookup Htypeeq]]]]]].
  destruct H3 as [Consname [ps_cons [ty_cons [Heq' [HNoDupcons [Hlookup_cons Htype_eq_cons]]]]]].
  inv Heq; clear Heq.
  inv Heq'; clear Heq'.
  unfold extend_dec_env in H_clause2.
  simpl in H_clause2.
  destruct l as [| a' as' ].
  - subst.
    specialize (H_match st).
    destruct H_match as [v_mat H_match].
    destruct H_match as [f_mat H_match].
    destruct H_match as [st_mat H_match].
    destruct H_match as [H_match list_inv_mat].
    specialize (H_clause1 eq_refl st_mat).
    destruct H_clause1 as [v_c1 H_clause1].
    destruct H_clause1 as [f_c1 H_clause1].
    destruct H_clause1 as [st_c1 H_clause1].
    destruct H_clause1 as [H_clause1 b_inv_c1].
    destruct (Compare_dec.lt_eq_lt_dec f_c1 f_mat) as [ [c1_lt_mat | c1_eq_mat] | mat_lt_c1 ]; do 3 eexists; split; simpl in *; subst.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq.
      subst; simpl.
      rewrite <- sem_env_id.
      eapply more_fuel_same_value.
      apply c1_lt_mat.
      eapply eval_or_match_inc_fuel_res.
      discriminate.
      rewrite H_clause1.
      reflexivity.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      rewrite <- sem_env_id.
      rewrite H_clause1.
      reflexivity.
      lia.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      rewrite <- sem_env_id.
      rewrite H_clause1.
      reflexivity.
      lia.
    + assumption.
  - specialize (H_match st).
    destruct H_match as [v_mat H_match].
    destruct H_match as [f_mat H_match].
    destruct H_match as [st_mat H_match].
    destruct H_match as [H_match list_inv_mat].
    destruct list_inv_mat as [v1 list_inv_mat].
    destruct list_inv_mat as [v2 list_inv_mat].
    destruct list_inv_mat as [v_mat_sub list_inv_l].
    destruct list_inv_l as [a_inv_v1 list_inv_v2].
    assert (a_inv a' v1 /\ list_INV A a_inv as' v2) as list_inv_hyp by (split; assumption).
    specialize (H_clause2 a' as' v1 v2 eq_refl list_inv_hyp st_mat).
    destruct H_clause2 as [v_c2 H_clause2].
    destruct H_clause2 as [f_c2 H_clause2].
    destruct H_clause2 as [st_c2 H_clause2].
    destruct H_clause2 as [H_clause2 b_inv_c2].
    destruct (Compare_dec.lt_eq_lt_dec f_c2 f_mat) as [ [c2_lt_mat | c2_eq_mat] | mat_lt_c2 ];
    do 3 eexists; split; simpl in *; subst.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      (* new *)
      break_match; simpl.
      (* end new*)
      * rewrite Hlookup_cons; simpl.
        rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
        simp pmatch; simpl.
        eapply more_fuel_same_value.
        apply c2_lt_mat.
        eapply eval_or_match_inc_fuel_res.
        discriminate.
        apply H_clause2.
      * assert (NoDup [l'_str; a_str]).
        { constructor.
          intro contra.
          inv contra.
          contradiction.
          inv H.
          constructor.
          intro contra.
          inv contra.
          constructor. }
        contradiction.
    + simp eval_or_match; simpl.
    + simp eval_or_match; simpl.
      rewrite H_match; simpl.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup_cons; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      break_match; simpl.
      * apply H_clause2.
      * assert (NoDup [l'_str; a_str]).
        { constructor.
          intro contra.
          inv contra.
          contradiction.
          inv H.
          constructor.
          intro contra.
          inv contra.
          constructor. }
        contradiction.
    + assumption.
    + simp eval_or_match; simpl.
      eapply more_fuel_same_value in H_match.
      unfold evaluate in H_match.
      rewrite H_match.
      simp eval_or_match; simpl.
      simp pmatch; simpl.
      rewrite Hlookup; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htypeeq; subst; simpl.
      destruct (string_dec a_str l'_str); try contradiction.
      rewrite Hlookup_cons; simpl.
      rewrite PeanoNat.Nat.eqb_eq in Htype_eq_cons; subst; simpl.
      simp pmatch; simpl.
      lia.
    + assumption.
Qed.
Definition list_env : sem_env val := {|
            sev := [];
            sec := [(Short "Cons", (2, TypeStamp "Cons" 0)); (Short "Nil", (0, TypeStamp "Nil" 0))]
          |}.

Definition cake_map := Dlet [] (Pvar "map")
  (EFun "f"
     (ELetrec
        [("map", "l",
          EMat (EVar (Short "l"))
            [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
             (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"],
              ECon (Some (Short "Cons"))
                [EApp Opapp [EVar (Short "f"); EVar (Short "a")];
                 EApp Opapp [EVar (Short "map"); EVar (Short "t")]])])]
        (EVar (Short "map")))).

Definition term0 := EVar (Short "l").
Definition EVAL_map0 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) :=
  forall env, EVAL env term0 (list_INV A AINV l).

Definition term1 := ECon (Some (Short "Nil")) [].
Definition EVAL_map1 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) :=
  forall env, EVAL env term1 (list_INV B BINV nil).

(* I'm not sure if P is always derivable. *)
Definition term2 := EVar (Short "f").
Definition EVAL_map2 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term2 (FUNC AINV BINV f).

Definition term3 := EVar (Short "a").
Definition EVAL_map3 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term3 (AINV a).

Definition term4 := EApp Opapp [term2;term3].
Definition EVAL_map4 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term4 (BINV (f a)).

(* Need to detect that this is the recursive call *)
Definition term5 := EVar (Short "map").
Definition EVAL_map5 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term5 (FUNC (list_INV A AINV) (list_INV B BINV) fixpoint).

Definition term6 := EVar (Short "t").
Definition EVAL_map6 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term6 (list_INV A AINV t).

Definition term7 := EApp Opapp [term5;term6].
Definition EVAL_map7 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term7 (list_INV B BINV (fixpoint t)).

Definition term8 := ECon (Some (Short "Cons")) [term4;term7].
Definition EVAL_map8 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) (a : A) (t : list A) (P : l = a::t) :=
  forall env, EVAL env term8 (list_INV B BINV ((f a)::(fixpoint t))).

Definition term9 := EMat term0
                         [(Pcon (Some (Short "Nil")) [], term1);
                          (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"], term8)
                         ].
Definition EVAL_map9 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) :=
  forall env, EVAL env term9 (list_INV B BINV (match l with
                                          | [] => []
                                          | a :: t => f a :: fixpoint t
                                          end)).

Print map.
(* Should this always be tied to term11 in the case of fix? *)
Definition term10 := EVar (Short "map").
Definition EVAL_map10 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) (fixpoint : list A -> list B) (l : list A) :=
  forall env, EVAL env term10 (FUNC (list_INV A AINV) (list_INV B BINV) fixpoint).

Definition term11 := ELetrec [("map", "l", term9)] term10.
Definition EVAL_map11 (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) (f : A -> B) :=
  forall env, EVAL env term11 (FUNC (list_INV A AINV) (list_INV B BINV) (fix map (l : list A) : list B := match l with
           | [] => []
           | a::t => f a :: map t
           end)).

Definition term12 := EFun "f" term11.
Definition EVAL_map12 (env : sem_env val) (A B : Type) (AINV : A -> val -> Prop) (BINV : B -> val -> Prop) :=
  EVAL env term12 (FUNC (FUNC AINV BINV) (FUNC (list_INV A AINV) (list_INV B BINV)) (fun f => fix map (l : list A) : list B := match l with
           | [] => []
           | a::t => f a :: map t
           end)).

Ltac solve_nsLookup := unfold nsLookup; reflexivity.

Theorem map_certificate_theorem : forall A B AINV BINV, EVAL_map12 list_env A B AINV BINV.
Proof.
  unfold EVAL_map12.
  intros A B AINV BINV.
  (* rename lemma *)
  apply function_eval_lemma.
  - (* ??? *)
    constructor.
    constructor.
    constructor.
  - intros f v fINV.
    unfold term11.
    apply EVAL_remove_EQ.
    + constructor.
      constructor.
    + intros l.
      induction l; apply EVAL_ELetrec; intros.
      * unfold term9.
        apply (simple_list_cases_inv' A (list B) AINV (list_INV B BINV) _ _ _ [] (fun x xs => f x :: map f xs) []).
        -- reflexivity.
        -- good_cons_env_solve. (* Praise be Ltac *)
        -- discriminate.
        -- unfold term0.
           eapply EVAL_EVar.
           unfold nsLookup; reflexivity.
           assumption.
        -- intros.
           eapply EVAL_ECon.
           instantiate (1 := []).
           reflexivity.
           unfold nsLookup; reflexivity.
           constructor.
           intros.
           inv H1.
           reflexivity.
        -- intros.
           unfold term8.
           eapply EVAL_ECon.
           ++ instantiate (1 := [(BINV (f x),term4);(list_INV B BINV (map f xs),term7)]).
              reflexivity.
           ++ unfold nsLookup; reflexivity.
           ++ inv H0.
           ++ inv H0.
      * unfold term9.
        apply (simple_list_cases_inv' A (list B) AINV (list_INV B BINV) _ _ _ [] (fun x xs => f x :: map f xs) (a::l)).
        -- apply f_equal. reflexivity.
        -- good_cons_env_solve.
        -- discriminate.
        -- unfold term0.
           apply EVAL_EVar with v0.
           unfold nsLookup; reflexivity.
           assumption.
        -- intros.
           inv H0.
        -- intros x xs v1 vs Heq [HAINV HlistINV].
           inv Heq. clear Heq.
           unfold term8.
           eapply EVAL_ECon.
           ++ instantiate (1 := [(BINV (f x),term4);(list_INV B BINV (map f xs),term7)]).
              reflexivity.
           ++ solve_nsLookup.
           ++ constructor.
              unfold term4.
              eapply app_evaluates_to.
              unfold term2.
              apply EVAL_EVar with v.
              solve_nsLookup.
              apply fINV.
              unfold term3.
              apply EVAL_EVar with v1.
              solve_nsLookup.
              assumption.
              constructor.
              unfold term7.
              simpl.
              eapply app_evaluates_to.
              (* need to figure out how to generalize this *)
              ** unfold term5.
                 generalize dependent IHl.
                 unfold EVAL.
                 unfold evaluate.
                 intros.
                 destruct (IHl st) as [v2 [f0 [st' [Heval feqINV]]]].
                 exists v2, f0, st'.
                 split.
                 simp eval_or_match in *; simpl in *.
                 break_if.
                 unfold term10 in Heval.
                 simp eval_or_match in Heval; simpl in *.
                 inv Heval.
                 apply feqINV.
              ** unfold term6.
                 eapply EVAL_EVar.
                 solve_nsLookup.
                 unfold EQ.
                 split; try reflexivity; try assumption.
              ** constructor.
           ++ intros.
              inv H0.
              inv H5.
              inv H7.
              simpl.
              exists y, y0.
              split.
              reflexivity.
              split; assumption.
Qed.

Definition decl0 := Dlet [] (Pvar "map")
  (EFun "f"
     (ELetrec
        [("map", "l",
          EMat (EVar (Short "l"))
            [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
             (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"],
              ECon (Some (Short "Cons"))
                [EApp Opapp [EVar (Short "f"); EVar (Short "a")];
                 EApp Opapp [EVar (Short "map"); EVar (Short "t")]])])]
        (EVar (Short "map")))).
