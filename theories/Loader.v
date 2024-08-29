Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import RefineInv.
Require Import EvaluateDecsWrapper.
Require Import EnvWrangling.
Declare ML Module "coq2cakeml:coq2cakeml.plugin".

Require Export RefineInv.
Require Export EvaluateDecsWrapper.
Require Export Equations.Prop.Equations.

Require Import Strings.String.
Open Scope string_scope.
(* GenerateInvariant list. *)
(* GenerateConstLemma nil. *)
(* Proof. *)
(*   intros. *)
(*   unfold EVAL in *; unfold evaluate in *. *)
(*   intro st. *)
(*   eexists. *)
(*   exists 0. *)
(*   eexists. *)
(*   simp eval_or_match in *; simpl. *)
(*   rewrite H; simpl. *)
(*   simp eval_or_match in *; simpl. *)
(*   simpl in *. *)
(*   unfold ident_string_beq in H. *)
(*   rewrite H; simpl. *)
(*   split; try reflexivity. *)
(* Qed. *)

(* Require Import Lists.List. *)
(* Import ListNotations. *)
(* Require Import Lia. *)
(* (* This is annoying *) *)
(* GenerateConstLemma cons. *)
(* Proof. *)
(*   intros. *)
(*   unfold EVAL in *; unfold evaluate in *; simpl in *. *)
(*   intro st. *)
(*   specialize (H1 st). *)
(*   destruct H1 as [v1 [f1 [st1 [Heval1 Hinv1]]]]. *)
(*   specialize (H0 st1). *)
(*   destruct H0 as [v0 [f0 [st0 [Heval0 Hinv0]]]]. *)
(*   apply (use_maximum_fuel _ [f0; f1]) in Heval1; try (unfold list_max; simpl; lia). *)
(*   apply (use_maximum_fuel _ [f0; f1]) in Heval0; try (unfold list_max; simpl; lia). *)
(*   do 3 eexists. *)
(*   simp eval_or_match in *; simpl. *)
(*   rewrite H; simpl in *. *)
(*   simp eval_or_match in *; simpl. *)
(*   rewrite Heval1; simpl. *)
(*   rewrite Heval0; simpl. *)
(*   unfold ident_string_beq in H. *)
(*   rewrite H; simpl. *)
(*   split. *)
(*   reflexivity. *)
(*   do 2 eexists. *)
(*   split. *)
(*   reflexivity. *)
(*   split; try assumption. *)
(* Qed. *)

(* Check EVAL_ECon_cons. *)
(* Inductive same_prod (A : Type) : Type := *)
(* | sprod : A -> A -> same_prod A. *)

(* Inductive doublelist (A : Type) : Type := *)
(* | dnil : doublelist A *)
(* | dcons : A -> A -> doublelist A -> doublelist A. *)

(* GenerateInvariant same_prod. *)
(* GenerateInvariant doublelist. *)

(* Testing doublelist. *)
(* Require Import CakeSem.CakeAST. *)
(* Require Import CakeSem.Namespace. *)
(* Print Forall. *)
(* Print Forall2. *)
(* Lemma nsLookup_head : forall V name (v : V) ns, *)
(*     nsLookup ident_string_beq (Short name) *)
(*       (nsBind name v ns) = Some v. *)
(* Proof. *)
(*   intros. *)
(*   unfold nsLookup. *)
(*   simpl. *)
(*   rewrite eqb_refl. *)
(*   reflexivity. *)
(* Qed. *)

(* FAKE ALL BELOW IS LIES *)


(* Definition modify_recclosure_additional_funs (v: val) (fe : list (string * string * exp)) : val := *)
(*   match v with *)
(*   | Recclosure e _ n => Recclosure e fe n *)
(*   | _ => v *)
(*   end. *)

(* Check build_rec_env. *)


(* Print fold_right. *)

(* Print build_rec_env. *)
(* Lemma fold_map_equiv_when : forall A B (f : B -> A) lb, *)
(*   fold_right (fun b la => (f b)::la) [] lb = map f lb. *)
(* Proof. *)
(*   induction lb. *)
(*   - reflexivity. *)
(*   - simpl. rewrite IHlb. *)
(*     reflexivity. *)
(* Qed. *)


(* (* HERE *) *)
(* Lemma idk_yet : forall funs cl_env, *)
(*     build_rec_env funs cl_env [] = map (fun '(n,_,_) => (Short n, Recclosure cl_env funs n)) funs. *)
(* Proof. *)
(*   unfold build_rec_env. *)
(*   intros. *)
(*   rewrite <- fold_map_equiv_when. *)
(*   assert *)
(*     ((fun (b : tvarN * tvarN * exp) (la : list (ident tvarN tvarN * val)) => *)
(*         (let '(n, _, _) := b in (Short n, Recclosure cl_env funs n)) :: la) *)
(*      = *)
(*        (fun '(f, _, _) (env' : namespace tvarN tvarN val) => nsBind f (Recclosure cl_env funs f) env')). *)
(*   apply functional_extensionality. *)
(*   destruct x as [[n v] b]. *)
(*   simpl. *)
(*   apply functional_extensionality. *)
(*   induction x. *)
(*   reflexivity. *)
(*   reflexivity. *)
(*   rewrite H. *)
(*   reflexivity. *)
(* Qed. *)

(* Print fold_right. *)
(* Lemma wierd1 : forall A B (xs : list A) (ts : list B) x f, *)
(*   fold_right (fun x t => (f x)::t) ts (x::xs) = *)
(*     (f x)::(fold_right (fun x t => (f x)::t) ts xs). *)
(* Proof. *)
(*   induction xs; intros; reflexivity. *)
(* Qed. *)

(* Lemma wierd : forall A B (f : B -> A) ts xs, *)
(*     fold_right (fun x t => ((f x)::t)) ts xs = *)
(*       (map f xs) ++ ts. *)
(* Proof. *)
(*   intros A B f ts xs. revert ts. *)
(*   induction xs; intros. *)
(*   - intros. reflexivity. *)
(*   - rewrite wierd1. *)
(*     simpl. *)
(*     rewrite IHxs. *)
(*     reflexivity. *)
(* Qed. *)

(* Print build_rec_env. *)

(* Lemma wierd1_but_giving_nsBind :  forall cl_env f funs added_env, *)
(* fold_right (fun '(n,_,_) env => nsBind n (Recclosure cl_env (f::funs) n) env) added_env (f::funs) = *)
(*     (@Short string string (fst (fst f)), (Recclosure cl_env (f::funs) (fst (fst f))))::(fold_right (fun '(n,_,_) env => nsBind n (Recclosure cl_env (f::funs) n) env) added_env funs). *)
(* Proof. *)
(*   simpl. *)
(*   destruct f as [[n v] b]. *)
(*   simpl. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma nsBind_as_fun : forall n v b funs env cl_env, *)
(*   nsBind n (Recclosure cl_env funs n) env = *)
(*     (fun (trip : (string * string * exp)) => *)
(*        let '(n',_,_) := trip in (@Short string string n', Recclosure cl_env funs n)::env) (n,v,b). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)


(* Fixpoint bre2 (funs : list (tvarN * tvarN * exp)) (funsagain : list (tvarN * tvarN * exp)) (cl_env : sem_env val) (add_to_env : env_val) := *)
(*   match funs with *)
(*   | [] => add_to_env *)
(*   | (n,v,b)::funs' => nsBind n (Recclosure cl_env funsagain n) (bre2 funs' funsagain cl_env add_to_env) *)
(*   end. *)

(* Print build_rec_env. *)

(* Definition build_rec_env' funs cl_env add_to_env := bre2 funs funs cl_env add_to_env. *)

(* Theorem build_rec_env'_eq_build_rec_env : forall funs cl_env add_to_env, *)
(*     build_rec_env funs cl_env add_to_env = build_rec_env' funs cl_env add_to_env. *)
(* Proof. *)
(*   induction funs; intros. *)
(*   reflexivity. *)
(*   unfold build_rec_env, build_rec_env'; simpl. *)
(*   destruct a as [[n v] b]; simpl. *)






(*                           Lemma idk2 : forall funs cl_env env, *)
(*       build_rec_env funs cl_env env = map (fun '(n,_,_) => (Short n, Recclosure cl_env funs n)) funs ++ env. *)
(* Proof. *)
(*   intros funs cl_env env. *)
(*   revert funs. revert cl_env. *)
(*   induction env. *)
(*   - intros.  rewrite app_nil_r. apply idk_yet. *)
(*   - induction funs. *)
(*     reflexivity. *)
(*     destruct a0 as [[n v] b]. *)
(*     unfold build_rec_env. *)
(*     simpl. *)


(* Lemma build_rec_env_app_rewrite : forall funs cl_env init_env, *)
(*     build_rec_env funs cl_env init_env = build_rec_env funs cl_env nsEmpty ++ init_env. *)
(* Proof. *)
(*   induction init_env. *)
(*   - rewrite app_nil_r. reflexivity. *)
(*   - unfold build_rec_env. simpl. *)


(*   induction funs. *)
(*   + reflexivity. *)
(*   + intros. destruct a as [[n v] b]. *)
(*     simpl in *. *)
(*     unfold build_rec_env. *)
(*     assert ((n,v,b)::funs = [(n,v,b)] ++ funs) by reflexivity. *)
(*     rewrite H. *)
(*     rewrite fold_right_app. *)









(*     Lemma build_rec_env_stuff' : forall funs cl_env new_env new_def, *)
(*       build_rec_env funs cl_env extended_env = new_env -> *)
(*       build_rec_env (new_def::funs) cl_env extended_env = (Short (fst (fst new_def)), Recclosure cl_env (new_def::funs) (fst (fst new_def)))). *)
(* Proof. *)



(* Theorem prettier_fixpoints_aka_the_white_whale : forall decs funs fuel st st' env env' locs, *)
(*     length decs >= 1 -> *)
(*     Forall2 (fun fun_def d => exists funname anyvar anybody, *)
(*                  d = Dlet locs (Pvar funname) (ELetrec funs (EVar (Short funname))) /\ *)
(*                    fun_def = (funname, anyvar, anybody)) *)
(*       funs decs -> *)
(*     evaluate_decs fuel st env decs = (st', Rval env') -> *)
(*     evaluate_decs fuel st env [Dletrec locs funs] = (st', Rval env'). *)
(* Proof. *)
(*   induction decs. *)
(*   - intros. *)
(*     inversion H. *)
(*   - induction decs. *)
(*     + clear IHdecs. intros. *)
(*       inversion H0. subst. *)
(*       inversion H6. subst. *)
(*       destruct H5 as [f [av [ab [Hd Hf]]]]. subst. *)
(*       rewrite <- H1. symmetry. *)
(*       apply singular_rec_fun_equiv_DLet_DLetrec. *)
(*     + clear IHdecs. clear IHdecs0. *)
(*       intros. revert H1. inversion H0. subst. clear H0. *)
(*       inversion H5. subst. clear H5. *)
(*       clear H6. *)
(*       destruct H4 as [f [av [ab [Hd Hf]]]]; subst. *)
(*       destruct H3 as [f' [av' [ab' [Hd' Hf']]]]; subst. *)
(*       clear H. *)
(*       simp evaluate_decs in *; simpl in *. *)
(*       simp eval_or_match; simpl. *)
(*       assert (f =? f' = false). admit. *)
(*       rewrite H. *)
(*       assert (string_in f (map (fun x => fst (fst x)) l0) = false). admit. *)
(*       rewrite H0. *)
(*       assert (string_in f' (map (fun x => fst (fst x)) l0) = false). admit. *)
(*       rewrite H1. *)
(*       assert (string_in f (map (fun '(x, _,_ ) =>  x) l0) = false). admit. *)
(*       rewrite H2. *)
(*       assert (string_in f' (map (fun '(x, _,_ ) =>  x) l0) = false). admit. *)
(*       rewrite H3. *)
(*       assert (nodup_str (map (fun '(x, _,_ ) =>  x) l0) = true). admit. *)
(*       assert (nodup_str (map (fun x => fst (fst x)) l0) = true). admit. *)
(*       rewrite H4. rewrite H5. *)
(*       unfold nsLookup. unfold lookup. *)
(*       unfold update_sev. simpl. *)
(*       rewrite eqb_refl. simpl. *)
(*       simp pmatch. *)
(*       unfold combine_dec_result. *)
(*       unfold extend_dec_env. simpl. *)
(*       simp evaluate_decs. *)
(*       simpl. *)
(*       rewrite H0. *)
(*       break_match. *)
(*       rewrite <- H1. *)
(*       break_match. *)
(*       break_match. *)
(*       break_match. *)
(*       break_match_hyp. *)
(*       break_match_hyp. *)
(*       simp pmatch in *. *)
(*       subst. *)
(*       simp eval_or_match in *. *)
(*       simpl in *. *)
(*       rewrite *)
















(*   intros. *)
(*   generalize dependent funs. *)
(*   funelim (evaluate_decs fuel st env decs); intros. *)
(*   - inversion H. *)
(*   - inversion H0; subst. *)
(*     destruct H5 as [locs' [funname [anyvar [anybody [Hdlet Hfun]]]]]. *)
(*     subst. *)
(*     inversion H6; subst; clear H6. *)
(*     inversion Hdlet; subst. *)
(*     simp evaluate_decs in *; simpl in *. *)
(*     simp eval_or_match in H1; simpl in H1. *)
(*     unfold build_rec_env in H1; simpl in H1. *)
(*     rewrite nsLookup_head in H1; simpl in *. *)
(*     simp pmatch in H1; simpl in *. *)
(*   - inversion H0; subst; clear H0. *)
(*     destruct H5 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   - inversion H0; subst; clear H0. *)
(*     destruct H5 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   - inversion H0; subst; clear H0. *)
(*     destruct H5 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   - inversion H0; subst; clear H0. *)
(*     destruct H5 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   - inversion H2; subst; clear H0. *)
(*     destruct H6 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   - inversion H3; subst; clear H0. *)
(*     destruct H7 as [lo [f [_ [_ [contra _]]]]]. *)
(*     inversion contra. *)
(*   -  inversion H3; subst; clear H3. *)
(*      destruct H7 as [locs' [funname [anyvar [anybody [Hdlet Hfun]]]]]; subst. *)
(*      destruct (evaluate_decs fuel st env *)
(*                  [Dlet locs' (Pvar funname) *)
(*                     (ELetrec ((funname, anyvar, anybody) :: l) (EVar (Short funname)))]). *)
(*      destruct r. *)
(*      destruct (evaluate_decs fuel s (extend_dec_env s0 env) (d2 :: decl')). *)
(*      eapply H0. *)
(*      constructor. *)
(*      constructor. *)
(*      constructor. *)
(*      constructor. *)
(*      admit. *)
(*      apply H2. *)




(*      clear H1. *)
(*      eapply H0. *)
(*      constructor. *)
(*      constructor. *)
(*      constructor. *)
(*      constructor. *)
(*      instantiate (1 := (d2::decl')). *)
(*      simpl. lia. *)
(*      apply H2. *)
