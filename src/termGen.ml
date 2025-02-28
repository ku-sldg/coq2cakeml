open Util
open EConstr
open TypeGen

let get_constructor refname =
  match Coqlib.lib_ref refname with
  | ConstructRef constn -> mkConstructU(constn, EInstance.empty)
  | _ -> failwith ("get_constructor: " ^ refname)

let get_constructor' parts = get_constructor (String.concat "." parts)

let get_nat_constr cname = get_constructor' ["num"; "nat"; cname]

(* let get_int_constr cname = get_constructor "BinInt" cname *)

let get_option_constr cname = get_constructor' ["core"; "option"; cname]

let get_list_constr cname = get_constructor' ["core"; "list"; String.lowercase_ascii cname]

let get_string_constr cname = get_constructor' ["core"; "string"; String.lowercase_ascii cname]

let get_ident_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_exp_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_lit_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

(* let get_opn_constr cname = get_constructor "CakeAST" cname *)

let get_op_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_pat_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_ast_t_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_dec_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_stamp_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let get_val_constr cname = get_constructor' ["cake"; String.lowercase_ascii cname]

let char_to_coq_ascii char =
  let ascii_const = get_constructor "core.ascii.ascii" in
  let true_const  = get_constructor "core.bool.true" in
  let false_const = get_constructor "core.bool.false" in
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

let rec int_to_coq_nat i =
  if i <= 0 then get_constructor "num.nat.O"
  else mkApp (get_constructor "num.nat.S", [| int_to_coq_nat (i - 1)|])

let rec str_to_coq_str str =
  if str = "" then get_string_constr "empty"
  else
    let chr = String.get str 0 in
    let coq_chr = char_to_coq_ascii chr in
    mkApp (get_string_constr "String", [| coq_chr; str_to_coq_str (String.sub str 1 (String.length str - 1))|])

let name_to_str ?(anon = "") name =
  let open Names in
  match name with
  | Anonymous -> anon
  | Name id -> Id.to_string id

let pair_to_coq_pair (x,y) xty yty =
  mkApp (get_constructor "core.prod.intro", [|xty; yty; x; y |])

let rec list_to_coq_list list typ =
  match list with
  | [] -> mkApp (get_list_constr "nil", [| typ |])
  | x::l -> mkApp (get_list_constr "cons", [| typ; x; list_to_coq_list l typ |])

let option_to_coq_option op typ =
  match op with
  | None -> get_option_constr "None"
  | Some x -> mkApp (get_option_constr "Some", [| typ; x |])

let rec ident_of_str ?(long = []) name_str =
  match long with
  | []   -> mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str name_str|])
  | h::t -> mkApp (get_ident_constr "Long",
                   [| string_type; string_type; str_to_coq_str h; ident_of_str ~long:t name_str|])

let mk_eq typ t1 t2 =
  mkApp (get_type "core.eq.type", [|typ; t1; t2|])

let get_dyn_constant module_name identifier_name =
  let const_qualid = Libnames.qualid_of_string (if module_name <> ""
                                                then String.concat "." [module_name; identifier_name]
                                                else identifier_name)
  in

  let constant =
    try Smartlocate.global_constant_with_alias const_qualid
    with
    | Nametab.GlobalizationError x -> failwith (String.cat "get_constant failed on: " (Libnames.string_of_qualid x))
  in
  mkConstU(constant,EInstance.empty)

let get_constant refname =
  match Coqlib.lib_ref refname with
  | ConstRef const -> mkConstU(const, EInstance.empty)
  | _ -> failwith ("get_constant " ^ refname)

let mk_nsBind () = get_constant "cake.nsbind"
let mk_extend_dec_env () = get_constant "cake.extend_dec_env"
let mk_nsEmpty () = get_constant "cake.nsEmpty"
let mk_Build_sem_env () = get_constructor "cake.Build_sem_env"

let mk_good_cons_env () = get_constant "cake.good_cons_env"

let unknown_loc () = list_to_coq_list [] nat_type

let mkFUNC typ1 typ2 inv1 inv2 = mkApp(get_constant "cake.func",[|typ1; typ2; inv1; inv2|])

let mkEVAL cake_env exp inv = mkApp(get_constant "cake.eval",[|cake_env; exp; inv|])

let mk_write_v name v env = mkApp(get_constant "cake.write_v", [|name; v; env|])

let mk_write_c name c env = mkApp(get_constant "cake.write_c", [|name; c; env|])

let mk_merge_envs env1 env2 = mkApp(get_constant "cake.merge_envs", [|env1; env2|])

let mk_write_rec funs cl_env env = mkApp(get_constant "cake.write_rec", [|funs; cl_env; env|])

let mk_write_c_list cs env = mkApp(get_constant "cake.write_c_list", [|cs; env|])

let curr_env_name = Summary.ref ~name:"curr_env_name" "cake_env"
let prev_env_name = Summary.ref ~name:"prev_env_name" "cake_env"
let next_env_num = Summary.ref ~name:"next_env_num" 0
let curr_st_num = Summary.ref ~name:"curr_st_num" 0
