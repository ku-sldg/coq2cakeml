(* Manipulating the pervasive semantic environment and state during translation *)
open EConstr
open TermGen
open TypeGen

(* let empty_sem_env () = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "SemanticsAux.empty_sem_env") *)
(* let empty_namespace () = *)
(*   Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "CakeSem.Namespace.nsEmpty") *)

let init_state_fun () =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.init_st")

let mk_init_state () = mkApp (mkConstU (init_state_fun (), EInstance.empty), [| TypeGen.nat_type ; TermGen.get_nat_constr "O" |])
let mk_state clk refs ffi ityp iexn =
  mkApp (get_constant "cake.build_state", [| nat_type ; clk; refs; ffi; ityp; iexn |])

let eval_decs_wrapper () =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper")

let apply_extend_dec_env new_env sem_env =
  mkApp (mk_extend_dec_env (), [| TypeGen.val_type; new_env; sem_env |])

let mk_empty_namespace mType nType vType = mkApp (mk_nsEmpty (), [| mType; nType; vType |])

let add_value_to_sem_env name cake_val sem_env =
  ()
let add_constructor_to_sem_env name cake_constructor sem_env =
  ()

let mk_empty_sem_env () = mkApp (get_constant "cake.empty_sem_env", [| TypeGen.val_type |])

let coq_fst sigma pair =
  let hd, args = destApp sigma pair in
  args.(2)

let coq_snd sigma pair =
  let hd, args = destApp sigma pair in
  args.(3)

(* sem_env val*)
let current_cake_env = Summary.ref ~stage:Interp ~name:"current_cake_env" (mk_empty_sem_env ())
let reset_current_cake_env () = current_cake_env := mk_empty_sem_env ()
let current_cake_st = Summary.ref ~stage:Interp ~name:"current_cake_st" (mk_init_state ())
let reset_current_cake_st () = current_cake_st := mk_init_state ()
let clear_semantic_environment () = reset_current_cake_env (); reset_current_cake_st ()
