(* Certificate Theorem Generation *)

open Extraction
open EConstr
open InvGen
open CakeEnv
open TermGen

let eval_dec decs env =
  let eval_decs_wrapper = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper") in
  mkApp (mkConst eval_decs_wrapper, [| mk_init_state; env; TermGen.list_to_coq_list decs TypeGen.dec_type |])

let create_certificate_theorem env cake_env term =
  let sigma = Evd.from_env env in
  let sigma',typ = Typing.type_of ~refresh:true env sigma term in
  let inv = invariant_from_type env typ in
  let exp = translate_term env term in
  let prods,decl = decompose_prod sigma inv in
  let rels = Array.init (List.length prods / 2) (fun x -> mkRel ((x + 1) * 2))
             |> Array.to_list |> List.rev |> Array.of_list in
  let decl' = mkApp (decl, [|mkApp (term, rels)|]) in
  let prods' = List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) prods in
  it_mkProd_or_LetIn (mkEVAL cake_env exp decl') prods'

(* Definition DECL (st : state ST) (env : sem_env val) (decs : list dec) (st' : state ST) (env' : sem_env val) *)
let create_decl_indiv_certificate_theorem start_st start_env dec final_st final_env =
  let decl_constant = mkConst (Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "DECL")) in
  mkApp (decl_constant,
         [| start_st; start_env;
            list_to_coq_list [dec] TypeGen.dec_type;
            final_st; final_env |])

let _ = Declare.declare_definition
    ~info:(Declare.Info.make ())
    ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string !curr_env_name) ~typ:(Some (TypeGen.sem_env_type TypeGen.val_type)) ())
    ~opaque:false
    ~body:mk_empty_sem_env
    (Evd.from_env (Global.env ()))

let mk_updated_environment ref cake_env_constant =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | IndRef (mut_name,index) ->
    let mut_body = Environ.lookup_mind mut_name global_env in
    let one_body = mut_body.mind_packets.(0) in

    let cons_names = one_body.mind_consnames in
    let cons_num_args = one_body.mind_consnrealargs in

    let open NameManip in
    let open TypeGen in
    let cake_cons_names = Array.map (fun name -> id_string_map name NameManip.cakeml_constructor_string |>
                                                 Names.Id.to_string |> str_to_coq_str) cons_names in
    let stamps =
      Array.map (fun name -> mkApp (get_stamp_constr "TypeStamp", [|name; int_to_coq_nat !curr_st_num |])) cake_cons_names
    in

    let cake_args = Array.map int_to_coq_nat cons_num_args in
    let nat_stamp_pairs = Array.map2 (fun x y -> pair_to_coq_pair (x,y) nat_type stamp_type)
        cake_args stamps
    in

    let cs = Array.map2 (fun x y -> pair_to_coq_pair (x,y) string_type (prod_type nat_type stamp_type))
        cake_cons_names nat_stamp_pairs |>
             Array.to_list |>
             List.rev |>
             (fun x -> list_to_coq_list x (prod_type string_type (prod_type nat_type stamp_type)))
    in
    mk_write_c_list cs cake_env_constant

  | ConstRef cname ->
    let body = Global.lookup_constant cname in
    let const_type = EConstr.of_constr body.const_type in
    let open NameManip in
    if isArity sigma const_type then cake_env_constant
    else
      let cake_name = id_of_constant cname |>
                      Names.Id.to_string |>
                      cakeml_variable_string |>
                      str_to_coq_str
      in
      let ebody =
        match body.const_body with
        | Def ebody -> ebody
        | _ -> raise (GenEx "update_environment: term to translate must be Defined and/or Transparent")
      in
      let e = translate_term global_env (EConstr.of_constr ebody) in
      let cake_val = mkApp (get_constant "EvaluateDecsWrapper" "wrapped_eval", [|e; cake_env_constant|]) in
      mk_write_v cake_name cake_val cake_env_constant

  | _ -> raise (GenEx "update_environment: not supported")

let update_environment ref =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  let new_env = mk_updated_environment ref (get_constant "" !curr_env_name) in

  prev_env_name := !curr_env_name;
  curr_env_name := String.concat "" ["cake_env"; string_of_int !next_env_num];
  next_env_num := !next_env_num + 1;

  let _ = Declare.declare_definition
            ~info:(Declare.Info.make ())
            ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string !curr_env_name) ~typ:(Some (TypeGen.sem_env_type TypeGen.val_type)) ())
            ~opaque:false
            ~body:new_env
            sigma
  in ()

let generate_invariant_and_update_environment ref =
  let glob_ref = locate_global_ref ref in
  match glob_ref with
  | IndRef _ ->
    InvGen.generate_refinement_invariant ref;
    let cake_dec = translate_declaration ref in
    add_dec_to_current_program cake_dec;
    update_environment ref;
    curr_st_num := !curr_st_num + 1

  | ConstRef _ ->
    InvGen.generate_refinement_invariant ref;
    let cake_dec = translate_declaration ref in
    add_dec_to_current_program cake_dec;
    update_environment ref

  | _ -> raise (UnsupportedFeature "must be a reference to an inductive type")

let generate_eval_certificate_theorem ~pm ~ref =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  let cake_dec = translate_declaration ref in
  let _ = add_dec_to_current_program cake_dec in
  update_environment ref;
  match glob_ref with
  | ConstRef const_name ->
    let x = Environ.lookup_constant const_name global_env in
    let certificate = begin
      match x.const_body with
      | Def const ->
        create_certificate_theorem global_env (get_constant "" !prev_env_name) (EConstr.of_constr const)
      | Undef _ -> raise (UnsupportedFeature "Axioms not supported")
      | _ -> raise (UnsupportedFeature "not doing this part right now")
    end in
    let certificate_theorem_name =
      const_name |> Names.Constant.label |> Names.Label.to_id
      |> Nameops.add_prefix "cake_" |> fun x -> Nameops.add_suffix x "_certificate_thm" in
    let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

    let open Declare in
    let pm = OblState.empty in
    let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
    let info = Info.make () in
    pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'

  | _ -> raise (UnsupportedFeature "need to come back here")

let generate_decl_certificate_theorem ~pm ~ref =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let open TypeGen in

  let st = mkApp (get_constant "SemanticsAux" "state_update_next_type_stamp", [|nat_type; mk_init_state; int_to_coq_nat !curr_st_num|]) in
  let st' = mkApp (get_constant "SemanticsAux" "state_update_next_type_stamp", [|nat_type; mk_init_state; int_to_coq_nat !curr_st_num|]) in
  let env = get_constant "" !prev_env_name in
  let open TypeGen in
  let default_val =
    mkApp (get_val_constr "Litv",
           [| mkApp (get_lit_constr "StrLit", [| str_to_coq_str "FAILURE: hd default" |]) |]) in
  let default_name =
    mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str "default"|]) in
  let default_prod =
    pair_to_coq_pair (default_name, default_val) (ident_type string_type string_type) val_type in
  let env' =
    mkApp (get_constructor "SemanticsAux" "" "Build_sem_env",
           [| val_type;
              list_to_coq_list [mkApp (get_constant "Lists.List" "hd",
                                       [| prod_type (ident_type string_type string_type) val_type;
                                          default_prod;
                                          mkApp (get_constant "SemanticsAux" "sev",
                                                 [| val_type; get_constant "" !curr_env_name |]) |])]
                (prod_type ident_str_type val_type);
              mkApp (get_constant "Namespace" "nsEmpty", [| string_type; string_type; prod_type nat_type stamp_type |]) |])
      in
  let cake_dec = translate_declaration ref in

  let certificate = create_decl_indiv_certificate_theorem st env cake_dec st' env' in

  let certificate_theorem_name =
    Nameops.add_prefix "DECL_indiv_" (Nameops.add_suffix (snd (Libnames.repr_qualid ref)) "_cert_thm") in

  let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

  let open Declare in
  let pm = OblState.empty in
  let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
  let info = Info.make () in
  pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'

let generate_program_decl_certificate_theorem ~pm prog_name =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let decl_constant = get_constant "" "DECL" in
  let rev_constant = get_constant "" "rev" in
  let certificate = mkApp (decl_constant,
                           [| mk_init_state; mk_empty_sem_env;
                              mkApp (rev_constant, [| TypeGen.dec_type; !current_program |]);
                              mkApp (get_constant "SemanticsAux" "state_update_next_type_stamp", [|TypeGen.nat_type; mk_init_state; int_to_coq_nat !curr_st_num|]);
                              get_constant "" !curr_env_name |])
  in

  let certificate_theorem_name = Nameops.add_prefix "cake_prog_" (Nameops.add_suffix (Names.Id.of_string prog_name) "_certificate_thm") in

  let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

  let open Declare in
  let pm = OblState.empty in
  let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
  let info = Info.make () in
  pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'
