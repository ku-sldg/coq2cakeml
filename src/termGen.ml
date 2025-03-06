open Util
open EConstr
open TypeGen

let get_constructor refname =
  match Coqlib.lib_ref refname with
  | ConstructRef constn -> mkConstructU(constn, EInstance.empty)
  | _ -> failwith ("get_constructor: " ^ refname)

let mk_O () = get_constructor "num.nat.O"
let mk_S ()  = get_constructor "num.nat.S"

let mk_None () = get_constructor "core.option.None"
let mk_Some () = get_constructor "core.option.Some"

let mk_nil () = get_constructor "core.list.nil"
let mk_cons () = get_constructor "core.list.cons"

let mk_pair () = get_constructor "core.prod.intro"

let mk_empty () = get_constructor "core.string.empty"
let mk_string () = get_constructor "core.string.string"

let mk_Short () = get_constructor "cake.short"
let mk_Long () = get_constructor "cake.long"

let mk_ELit () = get_constructor "cake.elit"
let mk_ECon () = get_constructor "cake.econ"
let mk_EVar () = get_constructor "cake.evar"
let mk_EFun () = get_constructor "cake.efun"
let mk_EApp () = get_constructor "cake.eapp"
let mk_EMat () = get_constructor "cake.emat"
let mk_ELet () = get_constructor "cake.elet"
let mk_ELetrec () = get_constructor "cake.eletrec"

let mk_StrLit () = get_constructor "cake.strlit"

let mk_Opapp () = get_constructor "cake.opapp"

let mk_Pvar () = get_constructor "cake.pvar"
let mk_PCon () = get_constructor "cake.pcon"
let mk_Pany () = get_constructor "cake.pany"

let mk_Atvar () = get_constructor "cake.atvar"
let mk_Atfun () = get_constructor "cake.atfun"
let mk_Attup () = get_constructor "cake.attup"
let mk_Atapp () = get_constructor "cake.atapp"

let mk_Dlet () = get_constructor "cake.dlet"
let mk_Dletrec () = get_constructor "cake.dletrec"
let mk_Dtype () = get_constructor "cake.dtype"
let mk_Dtabbrev () = get_constructor "cake.dtabbrev"

let mk_TypeStamp () = get_constructor "cake.typestamp"

let mk_Litv () = get_constructor "cake.litv"
let mk_Conv () = get_constructor "cake.conv"
let mk_Closure () = get_constructor "cake.closure"
let mk_Recclosure () = get_constructor "cake.recclosure"

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
    let args = Array.map (fun x -> if x then true_const else false_const) [| b1; b2; b3; b4; b5; b6; b7; b8 |]
    in
    mkApp (ascii_const, args)

  else mkApp (ascii_const, Array.make 8 false_const)

let rec int_to_coq_nat i =
  if i <= 0 then mk_O ()
  else mkApp (mk_S (), [| int_to_coq_nat (i - 1)|])

let rec str_to_coq_str str =
  if str = "" then mk_empty ()
  else let chr = String.get str 0 in
    let coq_chr = char_to_coq_ascii chr in
    mkApp (mk_string (), [| coq_chr; str_to_coq_str (String.sub str 1 (String.length str - 1))|])

(* wrong place for this *)
let name_to_str ?(anon = "") name =
  let open Names in
  match name with
  | Anonymous -> anon
  | Name id -> Id.to_string id

let pair_to_coq_pair (x,y) xty yty =
  mkApp (mk_pair (), [|xty; yty; x; y |])

let rec list_to_coq_list list typ =
  match list with
  | [] -> mkApp (mk_nil (), [| typ |])
  | x::l -> mkApp (mk_cons (), [| typ; x; list_to_coq_list l typ |])

let option_to_coq_option op typ =
  match op with
  | None -> mk_None ()
  | Some x -> mkApp (mk_Some(), [| typ; x |])

let rec ident_of_str ?(long = []) name_str =
  match long with
  | []   -> mkApp (mk_Short(), [| string_type(); string_type(); str_to_coq_str name_str|])
  | h::t -> mkApp (mk_Long(),
                   [| string_type(); string_type(); str_to_coq_str h; ident_of_str ~long:t name_str|])

let get_constant refname =
  match Coqlib.lib_ref refname with
  | ConstRef const -> mkConstU(const, EInstance.empty)
  | _ -> failwith ("get_constant " ^ refname)

let mk_nsBind () = get_constant "cake.nsbind"
let mk_extend_dec_env () = get_constant "cake.extend_dec_env"
let mk_nsEmpty () = get_constant "cake.nsempty"
let mk_Build_sem_env () = get_constructor "cake.Build_sem_env"

let mk_good_cons_env () = get_constant "cake.good_cons_env"

let unknown_loc () = list_to_coq_list [] (nat_type())

let mkFUNC typ1 typ2 inv1 inv2 = mkApp (get_constant "cake.func", [| typ1; typ2; inv1; inv2 |])

let mkEVAL cake_env exp inv = mkApp (get_constant "cake.eval", [| cake_env; exp; inv |])

let mk_write_v name v env = mkApp (get_constant "cake.write_v", [| name; v; env |])

let mk_write_c name c env = mkApp (get_constant "cake.write_c", [| name; c; env |])

let mk_merge_envs env1 env2 = mkApp (get_constant "cake.merge_envs", [| env1; env2 |])

let mk_write_rec funs cl_env env = mkApp (get_constant "cake.write_rec", [|funs; cl_env; env|])

let mk_write_c_list cs env = mkApp (get_constant "cake.write_c_list", [| cs; env |])

let curr_env_name = Summary.ref ~name:"curr_env_name" "cake_env"
let prev_env_name = Summary.ref ~name:"prev_env_name" "cake_env"
let next_env_num = Summary.ref ~name:"next_env_num" 0
let curr_st_num = Summary.ref ~name:"curr_st_num" 0
