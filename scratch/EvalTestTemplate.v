Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Open Scope string_scope.

Require Import CakeSem.ffi.FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.

Definition init_env : sem_env val := empty_sem_env.
Definition init_store := @empty_store val.

Parameter init_ffi_st : ffi_state nat.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Definition x := (Dtype [] [([], "nat", [("O", []); ("S", [Atapp [] (Short "nat")])])]).

Compute evaluate_decs 10 init_state empty_sem_env [x].
