(* Functions that generate Coq types *)

(* open Util *)
open EConstr

(* Smartlocate uses the names in the current environment. *)
(* So if for examples CakeAST has been imported then the qualified id wouldn't *)
(* necessarily need to be a full path. This raises the question of whether its *)
(* better to require full paths at all times in this source code or to instead *)
(* import the necessary modules before these functions get called from Coq. *)
(* let get_type module_name type_name = *)
(*   let type_qualid = Libnames.qualid_of_string (if module_name != "" *)
(*                                                then (String.concat "." [module_name; type_name]) *)
(*                                                else type_name) *)
(*   in *)
(*   let typ = *)
(*     try Smartlocate.global_inductive_with_alias type_qualid *)
(*     with *)
(*     | Nametab.GlobalizationError x -> failwith (String.cat "get_type failed on: " (Libnames.string_of_qualid x)) *)
(*   in *)
(*    mkIndU(typ, EInstance.empty) *)

let get_type reg_name =
  let glob_ref = Coqlib.lib_ref reg_name in
  match glob_ref with
  | Names.GlobRef.IndRef ind -> mkIndU(ind, EInstance.empty)
  | _ -> failwith reg_name

(* let nat_type () = get_type coq_init_mod "nat" *)
let nat_type = get_type "num.nat.type"

let string_type  = get_type "core.string.type"

let prod_type a_type b_type = mkApp (get_type "core.prod.type",
                                     [| a_type; b_type |])

let list_type a_type = mkApp (get_type "core.list.type",
                              [| a_type |])

let option_type a_type = mkApp (get_type  "core.option.type", [| a_type |])

let and_type a_type b_type = mkApp (get_type "core.and.type", [| a_type; b_type |])
let eq_type a_type a1 a2 = mkApp (get_type "core.eq.type", [| a_type; a1; a2 |])
let ex_type a_type a_to_prop = mkApp (get_type "core.ex.type", [| a_type; a_to_prop |])

let exp_type = get_type "cake.exp"
let pat_type  = get_type "cake.pat"
let ast_t_type = get_type "cake.ast_t"

let dec_type = get_type "cake.dec"
let stamp_type  = get_type "cake.stamp"
let val_type = get_type "cake.val"
let sem_env_type a_type = mkApp (get_type "cake.sem_env", [|a_type|])

let ident_type long_type short_type = mkApp (get_type "cake.ident",
                                             [| long_type; short_type|])

let ident_str_type () = ident_type string_type string_type
