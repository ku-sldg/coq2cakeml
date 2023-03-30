Require Import Constants.
Require Import String.
Open Scope string_scope.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import List.
Require RefineInv.
Import ListNotations.

Declare ML Module "coq2cakeml:coq2cakeml.plugin".

Definition dumb_plus x y := let z := x + y in z.
Eval cbv in "Test 1: lambda, let in".
TranslateDefine dumb_plus.
Print cake_dumb_plus.

Definition list_test := [O].
Eval cbv in "Test 2: 0 parameter constructor, 2 + 1 parameter constructor".
TranslateDefine list_test.
Print cake_list_test.

Eval cbv in "Test 3:".
Translate list.
TranslateDefine list.
Print cake_list.
(* Eval cbv in "Test 3: polymorphic, recursive function/fixpoint". *)
(* TranslateDefine map. *)
(* Print cake_map. *)

Eval cbv in "Test 4: polymorphic, recursive function/fixpoint and list invariant".
GenerateInvariant list.
Print list_INV.
TranslateDefine map.
Print cake_map.

Eval cbv in "Test 5: testing generatecertificate".
Print map.
GenerateCertificate map.
GenerateInvariant nat.
GenerateCertificate length.
GenerateCertificate plus.
GenerateInvariant prod.
GenerateCertificate fst.
Print cake_fst_certificate_thm.
(* Eval cbv in "Test 4: polymorphic, recursive function/fixpoint". *)
(* TranslateDefine length. *)
(* Print cake_length. *)

(* Inductive list' (A B : Type) : Type := *)
(* | nil' : list' A B *)
(* | cons' : A * B -> list' A B -> list' A B. *)

(* Inductive color := Red | Green | Blue. *)
(* Eval cbv in "Test 1.1: stuff". *)
(* GenerateInvariant nat. *)
(* GenerateInvariant bool. *)
(* GenerateInvariant list. *)
(* GenerateInvariant prod. *)
(* GenerateInvariant color. *)
(* GenerateInvariant list'. *)
