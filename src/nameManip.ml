let id_of_name ?(anon="x") n =
  let open Names in
  match n with
  | Anonymous -> Id.of_string anon
  | Name id -> id

let id_of_constant constant = Names.Constant.label constant |> Names.Label.to_id

let constant_inv_name constant = Nameops.add_suffix (id_of_constant constant)"_INV"

let id_string_map id (f : string -> string) =
  id |> Names.Id.to_string |> f |> Names.Id.of_string

(* CakeML name rules:
   1. Names start with an alpha
   2. Type names are lowercase and constructor names are uppercase
   3. type variables must start with '
 *)

(* exception NotACakeMLName of string *)

let cakeml_constructor_string str =
  (* if something then raise (NotACakeMLName str) *)
  String.capitalize_ascii str

let cakeml_variable_string str =
  (* if something then raise (NotACakeMLName str) *)
  String.uncapitalize_ascii str

let cakeml_type_variable_string str =
  (* if something then raise (NotACakeMLName str) *)
  (* let str' = ??? in *)
  String.concat "" ["'"; str]

(* does not currently handle contexts with two of the same name *)
let context_to_var_names context =
  let open Context.Rel.Declaration in
  List.map (fun d ->
      let id = get_name d |> id_of_name in
      let id_str = Names.Id.to_string id in
      cakeml_type_variable_string id_str)
    context
