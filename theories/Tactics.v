Require Import CakeMLExtraction.RefineInv.
Require Import Equations.Prop.Equations.

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Lia.

Require Import CakeSem.Evaluate.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import StructTact.StructTactics.

Ltac my_intros :=
  intros until env; intros Horig Hgood_cons Hmatched;
  repeat (match goal with
          | [|- EVAL _ _ _ ] => idtac
          | _ => let Hcase := fresh "Hcase" in intro Hcase end).

Ltac handle_good_cons :=
  unfold good_cons_env in *;
  match goal with
  | [good_cons : Forall ?P ((Pcon (Some (Short ?c_name)) ?args, ?c) :: ?t) |- _ ] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      let idk := fresh "idk" in
      let x := fresh "x" in
      let l := fresh "l" in
      inversion good_cons as [idk | x l H1 H2];
      clear good_cons;
      let con_name := fresh "con_name" in
      let ps := fresh "ps" in
      let ty := fresh "ty" in
      let Hps := fresh "Hps" in
      let HNo_Dup := fresh "HNo_Dup" in
      let Hlookup := fresh "Hlookup" in
      let Hstamp  := fresh "Hstamp" in
      destruct H1 as [con_name [ps [ty [Hps [HNo_Dup [Hlookup Hstamp]]]]]];
      inv Hps;
      apply PeanoNat.Nat.eqb_eq in Hstamp;
      subst
  | [good_cons : Forall ?P [] |- _ ] => clear good_cons
  end.

Ltac solve_max_fuel :=
  simpl; lia.

Ltac destruct_inv inv :=
  simpl in inv;
  match type of inv with
  | exists (_ : val), _ =>
      let v := fresh "match_arg_v" in
      let Hinv := fresh "Hinv" in
      destruct inv as
        [v Hinv];
      destruct_inv Hinv
  | ?P /\ ?Q =>
      let Heq := fresh "Heq" in
      let Hinv := fresh "Hinv" in
      let Hinv' := fresh "Hinv" in
      destruct inv as [Hinv Hinv'];
      subst;
      destruct_inv Hinv'
  | _ => subst
  end.

Ltac handle_matched :=
  match goal with
  | [H : EVAL ?env ?mat ?inv |- EVAL ?env (EMat ?mat ?pcs) ?res] =>
      let st := fresh "st" in
      intro st;
      unfold EVAL, evaluate in H;
      match goal with
      | [st : state nat |- _] =>
          specialize (H st);
          let v := fresh "matched_v" in
          let f := fresh "matched_f" in
          let st' := fresh "matched_st" in
          let Heval := fresh "Heval_match" in
          let Hinv := fresh "Hinv_match" in
          destruct H as [v [f [st' [Heval Hinv]]]];
          destruct_inv Hinv
      end

  end.

Ltac not_in_inequalities :=
  match goal with
  | [H : ~ In _ (_::_) |- _] =>
      let H' := fresh "H" in
      let Hineq := fresh "Hineq" in
      rewrite not_in_cons in H;
      destruct H as [Hineq H'];
      rewrite <- eqb_neq in Hineq;
      rewrite Hineq;
      clear Hineq
  end.

Ltac clean_up_NoDup :=
  match goal with
  | [H : ~ In _ [] |- _] => clear H
  | [H : NoDup [] |- _] => clear H
  end.

Ltac break_up_NoDup :=
  match goal with
  | [HNoDup : NoDup (_::_)  |- _ ] =>
      let fake := fresh "fake" in
      let x := fresh "x" in
      let l := fresh "l" in
      let HNotIn := fresh "HNotIn" in
      let HNoDup' := fresh "HNoDup" in
      inversion HNoDup as [fake | x l HNotIn HNoDup']; subst;
      clear HNoDup; repeat not_in_inequalities; clean_up_NoDup
  end.

Ltac handle_case Hcase :=
  match type of Hcase with
  | ?P -> EVAL _ _ _ =>
      cut P; try reflexivity;
      let H := fresh "H" in
      intro H
  end.

Ltac normalize_fuels fuels :=
  match goal with
  | [ H : eval_or_match _ _ ?f _ _ _ _ = _ |- _ ] =>
      tryif (constr_eq f (list_max fuels)) then fail
      else
        apply (use_maximum_fuel _ fuels) in H; try solve_max_fuel
  end.

Ltac handle_case_val_find_arg Hcase v :=
  match goal with
  | [ HvINV : ?INV ?arg v |- _] =>
      specialize (Hcase arg)
  end.

Ltac handle_case_val Hcase v := specialize (Hcase v).

Ltac handle_case_eq Hcase :=
  match type of Hcase with
  | ?q = ?q -> _ =>
      cut (q = q); try reflexivity;
      let H := fresh "H" in
      intro H;
      specialize (Hcase H);
      clear H
  end.

Ltac handle_case_inv Hcase :=
  match type of Hcase with
  | ?HINV -> ?rest =>
      match goal with
      | [Hfound : ?HINV |- _] =>
          specialize (Hcase Hfound)
      end
  end.

Ltac handle_case_break Hcase st :=
  specialize (Hcase st);
  let case_v := fresh "case_v" in
  let case_f := fresh "case_f" in
  let case_st := fresh "case_st" in
  let Hcaseeval := fresh Hcase "_eval" in
  let Hcaseinv := fresh Hcase "_inv" in
  destruct Hcase as
    [case_v [case_f [case_st [Hcaseeval Hcaseinv]]]].


Ltac solve_case_first_part Hcase args :=
  match args with
  | [] => idtac
  | ?v :: ?vs =>
      handle_case_val_find_arg Hcase v;
      solve_case_first_part Hcase vs
  end.

Ltac solve_case_second_part Hcase args :=
  match args with
  | [] => idtac
  | ?v :: ?vs =>
      handle_case_val Hcase v;
      solve_case_second_part Hcase vs
  end.

Ltac normalize_evaluate := unfold evaluate in *; simpl in *.

Ltac solve_case Hcase args st :=
  solve_case_first_part Hcase args;
  solve_case_second_part Hcase args;
  handle_case_eq Hcase;
  repeat handle_case_inv Hcase;
  handle_case_break Hcase st;
  normalize_evaluate.

(* Definition empty_args := @nil val. *)

Ltac In_solve := match goal with
                  | |- ~ In ?i [] => auto
                  | |- ~ In ?i ?l => intros [contra | rest]; [inv contra | In_solve]
                 | H : In ?i [] |- False => inv H
                 | H : In ?i ?l |- False => destruct H as [contra | rest]; [inv contra | In_solve]
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

(* For GenerateMatchLemma *)
Ltac final_solve_fst :=
  do 3 eexists;
  simp eval_or_match; simpl.

Ltac final_solve_rewrite_match :=
  match goal with
  | [H : eval_or_match true ?mat ?f ?st ?env uu uu = ?res |-
       context G [ eval_or_match true ?mat _ ?st ?env uu uu ]] =>
      rewrite H; simpl
  end.

Ltac final_solve_rewrite_nsLookups :=
  match goal with
  | H : nsLookup ident_string_beq ?name ?env = ?res |-
      context [nsLookup ident_string_beq ?name ?env] =>
      rewrite H; simpl
  end.


Ltac final_solve :=
  final_solve_fst;
  final_solve_rewrite_match;
  simp eval_or_match; simpl;
  simp pmatch; simpl;
  repeat final_solve_rewrite_nsLookups;
  simpl in *; try repeat break_up_NoDup; simpl in *; try clean_up_NoDup;
  simp pmatch; simpl in *;
  split;
  [ match goal with
    | [H : eval_or_match true ?case ?f ?st ?env ?uu ?uu = (?st',?val) |-
         context [eval_or_match true ?case ?f ?st ?env ?uu ?uu] ] =>
        apply H
    end |
    assumption ].

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
