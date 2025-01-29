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

Definition ST := nat.

Inductive ProgEq : val -> val -> Prop :=
| ValRefl : forall v, ProgEq v v
| ClosureEq :
  forall var (env env1 : sem_env val) (e e1 : exp) (v : val)
    env' env1' e' e1' st st' v' v1',
    do_opapp [Closure env var e; v] = Some (env',e') ->
    do_opapp [Closure env1 var e1; v] = Some (env1',e1') ->
    eval_rel st env' e' st' v' ->
    eval_rel st env1' e1' st' v1' ->
    ProgEq v' v1' ->
    ProgEq (Closure env var e) (Closure env1 var e1)
| BothClosureEq :
  forall var (env env1 : sem_env val) (e e1 : exp) name,
    (forall (v : val) env' env1' e' e1' st st' v' v1',
        do_opapp [Recclosure env [(name, var, e)] name; v] = Some (env',e') ->
        do_opapp [Closure env1 var e1; v] = Some (env1',e1') ->
        eval_rel st env' e' st' v' ->
        eval_rel st env1' e1' st' v1' ->
        ProgEq v' v1') ->
    ProgEq (Recclosure env [(name, var, e)] name) (Closure env1 var e1)
| BothClosureEqFlip :
  forall var (env env1 : sem_env val) (e e1 : exp) name,
    (forall (v : val) env' env1' e' e1' st st' v' v1',
        do_opapp [Closure env var e; v] = Some (env',e') ->
        do_opapp [Recclosure env1 [(name, var, e1)] name; v] = Some (env1',e1') ->
        eval_rel st env' e' st' v' ->
        eval_rel st env1' e1' st' v1' ->
        ProgEq v' v1') ->
    ProgEq (Closure env var e) (Recclosure env1 [(name, var, e1)] name).

Definition dtype_nat := Dtype [] [([], "nat", [("O",[]); ("S", [Atapp [] (Short "nat")])])].

Definition dletrec_plus_one := [dtype_nat;
                                Dletrec [] [("plus_one", "x", (ECon (Some (Short "S")) [(EVar (Short "x"))]))]].
Definition dlet_plus_one := [dtype_nat;
                             Dlet [] (Pvar "plus_one'") (EFun "x" (ECon (Some (Short "S")) [(EVar (Short "x"))]))].

Definition dtype_list := Dtype [] [(["'a"], "list", [("Nil", []); ("Cons", [Atvar "'a"; Atapp [Atvar "'a"] (Short "list")])])].

Definition dletrec_map := Dletrec [] [("map", "f",
                                        EFun "l" (EMat (EVar (Short "l"))
                                                    [(Pcon (Some (Short "Nil")) [],
                                                       ECon (Some (Short "Nil")) []);
                                                     (Pcon (Some (Short "Cons")) [Pvar "x"; Pvar "l'"],
                                                       ECon (Some (Short "Cons"))
                                                        [EApp Opapp [EVar (Short "f"); EVar (Short "x")];
                                                         EApp Opapp [EApp Opapp [EVar (Short "map"); EVar (Short "f")];
                                                                     EVar (Short "l'")]])]))].

Definition dlet_map :=
  Dlet [] (Pvar "map") (EFun "f"
                          (ELetrec [("map", "l", EMat (EVar (Short "l"))
                                                   [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
                                                    (Pcon (Some (Short "Cons")) [Pvar "x"; Pvar "l'"],
                                                      ECon (Some (Short "Cons")) [EApp Opapp [EVar (Short "f"); EVar (Short "x")]; EApp Opapp [EVar (Short "map"); EVar (Short "l'")]])])]
                                                        (EVar (Short "map")))).

Definition init_env : sem_env val := empty_sem_env.
Definition init_store := @empty_store val.

Parameter init_ffi_st : FFI.ffi_state nat.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Compute evaluate_decs 20 init_state init_env [dtype_list; dletrec_map].

Lemma __ : exists env st, evaluate_decs 20 init_state init_env [dtype_list; dlet_map] = (st, env).
  repeat eexists.
  unfold dtype_list, dlet_map; simpl.
  simp evaluate_decs; simpl.
  simp evaluate_decs; simpl.
  unfold evaluate.
  simp eval_or_match; simpl.
  simp pmatch; simpl.
  Admitted.

Example ex1 : ProgEq (Recclosure
   {|
     sev := [];
     sec :=
       [(Short "Cons", (2, TypeStamp "Cons" 0)); (Short "Nil", (0, TypeStamp "Nil" 0))]
   |}
   [("map", "f",
      EFun "l"
        (EMat (EVar (Short "l"))
           [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
            (Pcon (Some (Short "Cons")) [Pvar "x"; Pvar "l'"],
              ECon (Some (Short "Cons"))
                [EApp Opapp [EVar (Short "f"); EVar (Short "x")];
                 EApp Opapp
                   [EApp Opapp [EVar (Short "map"); EVar (Short "f")]; EVar (Short "l'")]])]))]
   "map")

  (Closure
     (extend_dec_env
        {|
          sev := nsEmpty;
          sec :=
            [(Short "Cons", (2, TypeStamp "Cons" 0)); (Short "Nil", (0, TypeStamp "Nil" 0))]
        |} init_env) "f"
     (ELetrec
        [("map", "l",
           EMat (EVar (Short "l"))
             [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
              (Pcon (Some (Short "Cons")) [Pvar "x"; Pvar "l'"],
                ECon (Some (Short "Cons"))
                  [EApp Opapp [EVar (Short "f"); EVar (Short "x")];
                   EApp Opapp [EVar (Short "map"); EVar (Short "l'")]])])]
        (EVar (Short "map")))).
constructor.
intros.
simpl in *.
inv H0; subst; clear H0.
inv H; subst; clear H.
unfold update_sev in *; simpl in *.
unfold eval_rel in *.
destruct H1.
destruct H2.
unfold evaluate in *.
simp eval_or_match in *; simpl in *.
break_match.
inv H; subst; clear H.
inv H0; subst; clear H0.
constructor.
intros.
simpl in *.
inv H0; subst; clear H0.
inv H; subst; clear H.
unfold eval_rel in *.
destruct H1.
destruct H2.
unfold evaluate in *.
simp eval_or_match in *; simpl in *.
simp eval_or_match in *; simpl in *.
Check pmatch.
break_match.
break_match.
inv H0.
inv H0.
unfold nsEmpty in *.
rewrite Heqm in H.
rewrite Heqm0 in H.
simp eval_or_match in *; simpl.
simp eval_or_match in *; simpl.
destruct x2.
simpl in *.
simp eval_or_match in *; simpl.
inv H0.
simpl in *.
simp eval_or_match in *; simpl.
destruct x2.
simpl in *.
simp eval_or_match in *; simpl.
inv H0.
simpl in *.
simp eval_or_match in *; simpl.
unfold nsLookup in *; simpl in *.
unfold nsAppend in *; simpl in *.
unfold build_rec_env in H2; simpl in *.
unfold nsBind in H2; simpl in *.








Example ex0 : ProgEq (Recclosure
  {|
    sev := [];
    sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))]
  |} [("plus_one", "x", ECon (Some (Short "S")) [EVar (Short "x")])] "plus_one")
(Closure
   {|
     sev := nsEmpty;
     sec := (Short "S", (1, TypeStamp "S" 0)) :: (Short "O", (0, TypeStamp "O" 0)) :: nsEmpty
   |} "x" (ECon (Some (Short "S")) [EVar (Short "x")])).
Proof.
  econstructor; simpl.
  - unfold update_sev, nsBind.
    simpl.
    reflexivity.
  - unfold update_sev, nsBind.
    simpl.
    reflexivity.
  - unfold eval_rel.
    eexists.
    unfold evaluate.
    simp eval_or_match; simpl.
    simp eval_or_match; simpl.
    reflexivity.
  - unfold eval_rel.
    eexists.
    unfold evaluate.
    simp eval_or_match; simpl.
    simp eval_or_match; simpl.
    reflexivity.
  - constructor.
    Unshelve.
    repeat constructor.
    repeat constructor.
    repeat constructor.
    repeat constructor.
Qed.

Example ex1 : ProgEq (Recclosure {| sev := []; sec := [] |}
                        [("id", "x", EVar (Short "x"))] "id")
                     (Closure {| sev := []; sec := [] |}
                       "x" (EVar (Short "x"))).
Proof.
  econstructor.
  - simpl; reflexivity.
  - simpl; reflexivity.
  - unfold eval_rel.
    eexists.
    unfold evaluate.
    simp eval_or_match; simpl.
    reflexivity.
  - unfold eval_rel.
    eexists.
    unfold evaluate.
    simp eval_or_match; simpl.
    reflexivity.
  - constructor.
    Unshelve.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
Qed.










  forall (v : val) (st : state ST) (e e1 : exp) var (env env1 : sem_env val),
    (exists (env' env1' : sem_env val) (e' e1' : exp) (st' : state ST) (u u1 : val),
      do_opapp [(Closure env var e); v]    = Some (env', e') /\ eval_rel st env' e' st' u ->
      do_opapp [(Closure env1 var e1); v] = Some (env1', e1') /\ eval_rel st env1' e1' st' u1 ->
      ProgEq u u1) ->
      ProgEq (Closure env var e) (Closure env1 var e1)
| RecclosureEq :
  forall (v : val) (st : state ST) (e e1 : exp) name var (env env1 : sem_env val),
    (exists (env' env1' : sem_env val) (e' e1' : exp) (st' : state ST) (u u1 : val),
        do_opapp [(Recclosure env  [(name, var, e)] name); v] = Some (env', e') /\ eval_rel st env' e' st' u ->
        do_opapp [(Recclosure env1 [(name, var, e1)] name); v] = Some (env1', e1') /\ eval_rel st env1' e1' st' u1 ->
      ProgEq u u1) ->
      ProgEq (Recclosure env  [(name, var, e)] name) (Recclosure env1 [(name, var, e1)] name)
| BothClosureEq :
  forall (v : val) (st : state ST) (e e1 : exp) name var (env env1 : sem_env val),
    (exists (env' env1' : sem_env val) (e' e1' : exp) (st' : state ST) (u u1 : val),
        do_opapp [(Closure env var e); v] = Some (env', e') /\ eval_rel st env' e' st' u ->
        do_opapp [(Recclosure env1 [(name, var, e1)] name); v] = Some (env1', e1') /\ eval_rel st env1' e1' st' u1 ->
      ProgEq u u1) ->
      ProgEq (Closure env var e) (Recclosure env1 [(name, var, e1)] name)
| BothClosureFlipEq :
  forall (e e1 : exp) name var (env env1 : sem_env val),
    (forall (v : val) (st : state ST), exists (env' env1' : sem_env val) (e' e1' : exp) (st' : state ST) (u u1 : val),

        do_opapp [(Recclosure env  [(name, var, e)] name); v] = Some (env', e') /\ eval_rel st env' e' st' u ->
        do_opapp [(Closure env1 var e1); v] = Some (env1', e1') /\ eval_rel st env1' e1' st' u1 ->
      ProgEq u u1) ->
      ProgEq (Recclosure env [(name, var, e)] name) (Closure env1 var e1).

Definition init_env : sem_env val := empty_sem_env.
Definition init_store := @empty_store val.

Parameter init_ffi_st : FFI.ffi_state nat.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.


Definition dletrec_ex := Dletrec [] [("id", "x", EVar (Short "x"))].
Definition dlet_ex := Dlet [] (Pvar "id") (EFun "x"  (EVar (Short "x"))).

Example ex1 : ProgEq (Recclosure {| sev := []; sec := [] |}
                        [("id", "x", EVar (Short "x"))] "id")
                     (Closure {| sev := []; sec := [] |}
                       "x" (EVar (Short "x"))).
Proof.
  constructor.
  intros.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  intros.
  destruct H, H0.
  unfold do_opapp in *.
  simpl in *.
  unfold update_sev in *; unfold nsBind in *; simpl in *.
  unfold build_rec_env in *; unfold nsBind in *; simpl in *.
  inv H; clear H.
  inv H0; clear H0.
  rewrite <- H5 in H1.
  rewrite <- H4 in H1.
  rewrite <- H3 in H2.
  rewrite <- H6 in H2.
  unfold eval_rel in *.
  destruct H1, H2.
  clear H5 H4 H3 H6.
  simpl in *.
  unfold evaluate in *.
  simp eval_or_match in *; simpl in *.
  inv H. inv H0.
  rewrite <- H3.
  Unshelve.
  repeat constructor.
  repeat constructor.
  apply ELit.
  constructor.
  constructor.
  apply ELit.
  constructor.
  constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
Qed.
