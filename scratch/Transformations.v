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

Add ML Path  "../_build/default/src".
Declare ML Module "coq2cakeml:coq2cakeml.plugin".

Definition ST := nat.

(* Definition cake_map := Dlet [] (Pvar "map") *)
(*   (EFun "f" *)
(*      (ELetrec *)
(*         [("map", "l", *)
(*           EMat (EVar (Short "l")) *)
(*             [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []); *)
(*              (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"], *)
(*               ECon (Some (Short "Cons")) *)
(*                 [EApp Opapp [EVar (Short "f"); EVar (Short "a")]; *)
(*                  EApp Opapp [EVar (Short "map"); EVar (Short "t")]])])] *)
(*         (EVar (Short "map")))). *)

(* Definition cake_length := Dlet [] (Pvar "length") *)
(*   (ELetrec *)
(*      [("length", "l", *)
(*        EMat (EVar (Short "l")) *)
(*          [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "O")) []); *)
(*           (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "l'"], *)
(*            ECon (Some (Short "S")) *)
(*              [EApp Opapp [EVar (Short "length"); EVar (Short "l'")]])])] *)
(*      (EVar (Short "length"))). *)
TranslateDefine length.
TranslateDefine map.

Fixpoint lamgen (lambdas : list string) (body : exp):=
  match lambdas with
  | [] => body
  | h::t => EFun h (lamgen t body)
  end.

Definition optimizer (d : dec) : dec :=
  let fix helper (e : exp) (toplevel_name : string) (lambdas : list string) :=
    match e with
    | EFun name body => helper body toplevel_name (app lambdas [name])
    | ELetrec [(name', arg, body')] (EVar (Short name'')) =>
        if andb (String.eqb toplevel_name name') (String.eqb name' name'')
        then Dletrec [] [(toplevel_name, hd arg lambdas, lamgen (tl lambdas) body')]
        else d
    | _ => d
    end
  in
  match d with
  | Dlet _ (Pvar name) body => helper body name []
  | _ => d
  end.

Compute (optimizer cake_length).
Compute (optimizer cake_map).

Definition init_env : sem_env val := empty_sem_env.
Definition init_store := @empty_store val.

Parameter init_ffi_st : FFI.ffi_state nat.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Example ex1 : evaluate_decs 10 init_state init_env [cake_length] =
                evaluate_decs 10 init_state init_env [optimizer cake_length].
Proof.
  unfold cake_length.
  simpl.
  simp evaluate_decs.
  assert (NoDup ["length"]).
  constructor.
  intro contra.
  inv contra.
  constructor.
  simpl.
  (* break_match. *)
  (* unfold init_env, init_state in *. *)
  (* unfold evaluate in Heqp. *)
  unfold evaluate.
  simp eval_or_match.
  simpl.
  break_if.
  unfold build_rec_env.
  simpl.
  simp pmatch.
  simpl.
  unfold nsBind.
  reflexivity.
  contradiction.
Qed.


Require Import RefineInv.
Print app_returns.
Print eval_rel.

Check Dletrec.
Check Dlet.

Definition dletrec_ex := Dletrec [] [("id", "x", EVar (Short "x"))].
Definition dlet_ex := Dlet [] (Pvar "id") (EFun "x"  (EVar (Short "x"))).
Example __ : exists st env, (evaluate_decs 10 init_state init_env [dlet_ex]) = (st, env).
Proof.
  eexists.
  eexists.
  unfold dlet_ex.
  simp evaluate_decs; simpl.
  unfold evaluate.
  simp eval_or_match; simpl.
  simp pmatch.
  simpl.


Theorem optimizer_good_sing : forall st env d f, evaluate_decs f st env [d] = evaluate_decs f st env [optimizer d].




Theorem optimizer_good_sing : forall st env d f, evaluate_decs f st env [d] = evaluate_decs f st env [optimizer d].
Proof.
  intros.
  induction d; try (reflexivity).
  simpl.
  break_match; subst; try reflexivity; simpl.
  destruct e; try reflexivity; simpl.
  simp evaluate_decs; simpl.
  unfold evaluate; simp eval_or_match; simpl.
  simp pmatch; simpl.
  simp
  break_match.
  break_match.
  simp pmatch.
  unfold alist_to_ns.
  unfold build_rec_env in *.
  simpl.
  break_match.
  apply andb_prop in Heqb.
  destruct Heqb.
  rewrite Strings.String.eqb_eq in H.
  rewrite Strings.String.eqb_eq in H0.
  subst.
  simpl in *.
  unfold eval_or_match_unfold_clause_6 in Heqp3.
  (* gonna need to start doing lookup theorems *)
  unfold nsLookup in Heqp3.
  simpl in Heqp3.
  Print Strings.String.
  rewrite String.eqb_refl in Heqp3.
  inv Heqp3.
  simpl.
  reflexivity.
  inv Heqp3.
  break_match.
  unfold update_sev in *.
  unfold nsLookup in *.
  simpl in *.
  apply andb_prop in Heqb.
  destruct Heqb.
  Print Strings.String.
  rewrite eqb_sym in Heqp3.
  rewrite H0 in Heqp3.
  simpl in *.
  inv Heqp3.
  assert (NoDup [s0]).
  constructor.
  intro contra.
  inv contra.
  constructor.
  contradiction.
Qed.
