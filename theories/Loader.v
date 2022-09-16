Require Import Constants.
Require Import String.
Open Scope string_scope.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import List.
Import ListNotations.

Add ML Path  "../_build/default/src".
Declare ML Module "coq2cakeml".

(* Definition nat_test_O : nat := O. *)
(* Eval cbv in "Test 1: 0 parameter constructor". *)
(* Translate nat_test_O. *)

Definition dumb_plus x y := let z := x + y in z.
Eval cbv in "Test 2: lambda, let in, plus".
Print dumb_plus.
Translate dumb_plus.

Definition add_one x := S x.
Eval cbv in "Test 3: lambda, 1 parameter constructor".
Translate add_one.

Definition list_test := [O].
Eval cbv in "Test 4: 0 parameter constructor, 2 + 1 parameter constructor".
Translate list_test.

Definition vector_test := Vector.cons _ 1 O (Vector.nil _).
Eval cbv in "Test 5: dependent constructor, 2 + 2 parameter constructor".
Translate vector_test.

Eval cbv in "Test 7: lambda, type arguments to functions".
Translate id.

Eval cbv in "Test 8: recursive function, type arguments to functions".
Print Datatypes.length.
Translate length.

Eval cbv in "Test 9: recursive function, higher order function, lambda, type arguments to functions".
Translate map.

Eval cbv in "Test 10: recursive function, match statement, lambda".
Translate plus.

Eval cbv in "Test 11: match statement, match on any, lambda".
Definition dumb_list l := match l with
                          | x::y::l' => x + y
                          | _ => 0
                          end.
Translate dumb_list.

Inductive colors : Set :=
| Yellow
| Blue
| Greeen
| Red
| Purple.

Definition color_match c := match c with
                            | Yellow => 0
                            | Red => 1
                            | _ => 2
                            end.
Eval cbv in "Test 12: match statement, match on any ".
Translate color_match.

Eval cbv in "Test 13: mutually recursive function".
Inductive tree (A B : Set) : Set := node : A -> forest A B -> tree A B
with forest (A B : Set) : Set :=
| leaf : B -> forest A B
| tr_cons : tree A B -> forest A B -> forest A B.
Fixpoint tree_size (A B : Set) (t:tree A B) : nat :=
                             match t with
                             | node _ _ a f => S (forest_size A B f)
                             end
with forest_size (A B : Set) (f:forest A B) : nat :=
                               match f with
                               | leaf _ _ b => 1
                               | tr_cons _ _ t f' => (tree_size A B t + forest_size A B f')
                               end.

Translate tree_size.
Translate forest_size.

Eval cbv in "Test 14: recursive let, higher order function, lambda, type arguments to functions".
Definition hide_map (A B : Type) (f : A -> B) l :=
  let fix real_map l' :=
    match l' with
    | nil => nil
    | cons x l'' => cons (f x) (real_map l'')
    end
  in real_map l.
Translate hide_map.

Eval cbv in "Test 14: type synonym".
Definition nat' := nat.
Translate nat'.

Eval cbv in "Test 15: Inductive type, no param".
Translate nat.

Eval cbv in "Test 16: Inductive type, one param".
Translate list.

Eval cbv in "Test 17: Inductive type, two params, mutually recursive".
Translate tree.

Eval cbv in "Test 18: Inductive type, zero? params, let binding of params".
Inductive nat_list (A := nat : Type) : Type :=
| nat_nil : nat_list
| nat_cons : A -> nat_list -> nat_list.
Translate nat_list.

Eval cbv in "Test 19: just a constructor".
Translate S.

Eval cbv in "Test 20: applying a recursive function".
Definition mapply := (map S [1;2;3]).
Translate mapply.

Eval cbv in "Test 21: extract constructor as function".
Definition my_succ := S.
Translate my_succ.
