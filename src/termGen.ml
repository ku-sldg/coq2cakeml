open Util
open Constr
open TypeGen

let get_constructor module_name type_name constructor_name =
  let const_qualid = Libnames.qualid_of_string (if module_name != ""
                                                then (String.concat "." [module_name; constructor_name])
                                                else constructor_name)
  in
  let constr = Smartlocate.global_constructor_with_alias const_qualid in
  mkConstruct constr

let get_int_constr cname = get_constructor "BinInt" "Z" cname

let get_option_constr cname = get_constructor "" "option" cname

let get_list_constr cname = get_constructor "" "list" cname

let get_string_constr cname = get_constructor "Strings.String" "string" cname

let get_ident_constr cname = get_constructor "Namespace" "ident" cname

let get_exp_constr cname = get_constructor "CakeAST" "exp" cname

let get_lit_constr cname = get_constructor "CakeAST" "lit" cname

let get_opn_constr cname = get_constructor "CakeAST" "opn" cname

let get_op_constr cname = get_constructor "CakeAST" "op" cname


let get_pat_constr cname = get_constructor "CakeAST" "pat" cname

let get_ast_t_constr cname = get_constructor "CakeAST" "ast_t" cname

let char_to_coq_ascii char =
  let ascii_const = get_constructor "Strings.Ascii" "ascii" "Ascii" in
  let true_const  = get_constructor "" "bool" "true" in
  let false_const = get_constructor "" "bool" "false" in
  let code = Char.code char in

  if code <= 255 && code >= 0 then
    let test_bit cc bitnum = (code / bitnum) mod 2 = 1 in
    let b1 = test_bit code 1 in (* ones place *)
    let b2 = test_bit code 2 in
    let b3 = test_bit code 4 in
    let b4 = test_bit code 8 in
    let b5 = test_bit code 16 in
    let b6 = test_bit code 32 in
    let b7 = test_bit code 64 in
    let b8 = test_bit code 128 in
    let args = Array.map (fun x -> if x then true_const else false_const) [| b1; b2; b3; b4; b5; b6; b7; b8 |] in

    mkApp (ascii_const, args)

  else mkApp (ascii_const, Array.make 8 false_const)

let rec str_to_coq_str str =
  if str = "" then get_string_constr "EmptyString"
  else
    let chr = String.get str 0 in
    let coq_chr = char_to_coq_ascii chr in
    mkApp (get_string_constr "String", [| coq_chr; str_to_coq_str (String.sub str 1 (String.length str - 1))|])

let name_to_str ?(anon = "") ba =
  let open Context in
  let open Names in
  match ba.binder_name with
  | Anonymous -> anon
  | Name id -> Id.to_string id

let pair_to_coq_pair (x,y) xty yty =
  mkApp (get_constructor "Coq.Init.Datatypes" "prod" "pair", [|xty; yty; x; y |])

let rec list_to_coq_list list typ =
  match list with
  | [] -> mkApp (get_list_constr "nil", [| typ |])
  | x::l -> mkApp (get_list_constr "cons", [| typ; x; list_to_coq_list l typ |])

let rec ident_of_str ?(long = []) name_str =
  match long with
  | []   -> mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str name_str|])
  | h::t -> mkApp (get_ident_constr "Long",
                   [| string_type; string_type; str_to_coq_str h; ident_of_str ~long:t name_str|])
