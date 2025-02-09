(* Functions that generate Coq types *)

open Util
open EConstr

(* Smartlocate uses the names in the current environment. *)
(* So if for examples CakeAST has been imported then the qualified id wouldn't *)
(* necessarily need to be a full path. This raises the question of whether its *)
(* better to require full paths at all times in this source code or to instead *)
(* import the necessary modules before these functions get called from Coq. *)
let get_type module_name type_name =
  let type_qualid = Libnames.qualid_of_string (if module_name != ""
                                               then (String.concat "." [module_name; type_name])
                                               else type_name)
  in
  let typ =
    try Smartlocate.global_inductive_with_alias type_qualid
    with
    | Nametab.GlobalizationError x -> failwith (String.cat "get_type failed on: " (Libnames.string_of_qualid x))
  in
   mkIndU(typ, EInstance.empty)


let coq_init_mod = "Coq.Init.Datatypes"
let coq_init_logic = "Coq.Init.Logic"

let nat_type () = get_type coq_init_mod "nat"

let string_type () = get_type "Strings.String" "string"

let prod_type a_type b_type = mkApp (get_type coq_init_mod "prod",
                                     [| a_type; b_type |])

let list_type a_type = mkApp (get_type coq_init_mod "list",
                              [| a_type |])

let option_type a_type = mkApp (get_type coq_init_mod "option", [| a_type |])

let and_type a_type b_type = mkApp (get_type coq_init_logic "and", [| a_type; b_type |])
let eq_type a_type a1 a2 = mkApp (get_type coq_init_logic "eq", [| a_type; a1; a2 |])
let ex_type a_type a_to_prop = mkApp (get_type coq_init_logic "ex", [| a_type; a_to_prop |])

let cake_ast_mod = "CakeSem.CakeAST"
let exp_type () = get_type cake_ast_mod "exp"
let pat_type () = get_type cake_ast_mod "pat"
let ast_t_type () = get_type cake_ast_mod "ast_t"

let _ = prod_type (nat_type ()) (nat_type ())

let dec_type () = get_type cake_ast_mod "dec"
let cake_semanticsaux_mod = "CakeSem.SemanticsAux"
let stamp_type () = get_type cake_semanticsaux_mod "stamp"
let val_type () = get_type cake_semanticsaux_mod "val"
let sem_env_type a_type = mkApp (get_type cake_semanticsaux_mod "sem_env", [|a_type|])

let cake_namespace_mod = "CakeSem.Namespace"
let ident_type long_type short_type = mkApp (get_type cake_namespace_mod "ident",
                                             [| long_type; short_type|])

let ident_str_type () = ident_type (string_type ()) (string_type ())
