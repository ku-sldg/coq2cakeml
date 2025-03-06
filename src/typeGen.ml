open EConstr

let get_type reg_name =
  let glob_ref = Coqlib.lib_ref reg_name in
  match glob_ref with
  | Names.GlobRef.IndRef ind -> mkIndU(ind, EInstance.empty)
  | _ -> failwith ("get_type: " ^ reg_name)

let nat_type () = get_type "num.nat.type"
let string_type ()  = get_type "core.string.type"
let prod_type a_type b_type = mkApp (get_type "core.prod.type", [| a_type; b_type |])
let list_type a_type = mkApp (get_type "core.list.type", [| a_type |])
let option_type a_type = mkApp (get_type  "core.option.type", [| a_type |])
let and_type a_type b_type = mkApp (get_type "core.and.type", [| a_type; b_type |])
let eq_type a_type a1 a2 = mkApp (get_type "core.eq.type", [| a_type; a1; a2 |])
let ex_type a_type a_to_prop = mkApp (get_type "core.ex.type", [| a_type; a_to_prop |])
let exp_type () = get_type "cake.exp"
let pat_type () = get_type "cake.pat"
let ast_t_type () = get_type "cake.ast_t"
let dec_type () = get_type "cake.dec"
let stamp_type () = get_type "cake.stamp"
let val_type () = get_type "cake.val"
let sem_env_type a_type = mkApp (get_type "cake.sem_env", [|a_type|])
let ident_type long_type short_type = mkApp (get_type "cake.ident", [| long_type; short_type|])
let ident_str_type () = ident_type (string_type ()) (string_type ())
