(* Certificate Theorem Generation *)
open Extraction
open EConstr
open InvGen
open CakeEnv
open TermGen

let eval_dec decs env =
  let eval_decs_wrapper = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper") in
  mkApp (mkConstU (eval_decs_wrapper, EInstance.empty), [| mk_init_st (); env; TermGen.list_to_coq_list decs (TypeGen.dec_type ()) |])

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

(* explodes on a polymorphic type *)
let create_axiom_cert_thm env cake_env axiom_name axiom_type =
  let sigma = Evd.from_env env in
  let inv = invariant_from_type env axiom_type in
  let exp = translate_axiom_exp env axiom_type in
  let _prods, _bottom_inv = decompose_prod sigma inv in
  let rels = Array.init (List.length _prods / 2) (fun x -> mkRel ((x + 1) * 2))
             |> Array.to_list |> List.rev |> Array.of_list in
  let inv' = mkApp (_bottom_inv, [|mkApp (mkConstU (axiom_name, EInstance.empty), rels)|]) in
  let prods' = List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) _prods in
  it_mkProd_or_LetIn (mkEVAL cake_env exp inv') prods'

(* Definition DECL (st : state ST) (env : sem_env val) (decs : list dec) (st' : state ST) (env' : sem_env val) *)
let create_decl_indiv_certificate_theorem start_st start_env dec final_st final_env =
  let decl_constant = mkConstU (Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "DECL"), EInstance.empty) in
  mkApp (decl_constant,
         [| start_st; start_env;
            list_to_coq_list [dec] (TypeGen.dec_type ());
            final_st; final_env |])

(* Initialize OCaml references and Rocq declarations that will be carried across *)
(* a translation session. This is my current solution to vs-coq problems. *)
let init_cake_env () =
  current_cake_env := mk_empty_sem_env ();
  current_cake_st := mk_init_st ();
  current_program := list_to_coq_list [] (TypeGen.dec_type ());
  curr_st_num := 0;

  let _ = Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string !curr_env_name) ~typ:(Some (TypeGen.sem_env_type (TypeGen.val_type ()))) ())
      ~opaque:false
      ~body:(mk_empty_sem_env ())
      (Evd.from_env (Global.env ()))
  in ()

(* Dangerous function to add *)
let create_val_axiom name =
  let hopefully_unique_name = Nameops.add_suffix name "_arb_v" in
  let _ = ComAssumption.declare_axiom
      ~coe:NoCoercion
      ~local:ImportDefaultBehavior
      ~kind:Definitional
      ~univs:(Evd.univ_entry ~poly:false Evd.empty)
      ~impargs:[]
      ~inline:NoInline
      ~name:hopefully_unique_name
      (EConstr.to_constr (Evd.empty) (TypeGen.val_type ()))
  in ()

let mk_updated_environment ref cake_env_constant =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let open TypeGen in
  let string_type = string_type () in
  let nat_type = nat_type () in
  let stamp_type = stamp_type () in

  match glob_ref with
  | IndRef (mut_name,index) ->
    let mut_body = Environ.lookup_mind mut_name global_env in
    let one_body = mut_body.mind_packets.(0) in

    let cons_names = one_body.mind_consnames in
    let cons_num_args = one_body.mind_consnrealargs in

    let open NameManip in
    let cake_cons_names = Array.map (fun name -> id_string_map name NameManip.cakeml_constructor_string |>
                                                 Names.Id.to_string |> str_to_coq_str) cons_names in
    let stamps =
      Array.map (fun name -> mkApp (mk_TypeStamp (), [| name; int_to_coq_nat !curr_st_num |])) cake_cons_names
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
      let cake_val =
        match body.const_body with
        | Def ebody ->
          let e = translate_term global_env (EConstr.of_constr ebody) in
          mkApp (get_constant "cake.wrapped_eval", [| e; cake_env_constant |])
        | Undef _ ->
          let _ = create_val_axiom @@ id_of_constant cname in
          let new_ax =
            Smartlocate.global_constant_with_alias (Libnames.qualid_of_string @@ Names.Id.to_string @@ Nameops.add_suffix (id_of_constant cname) "_arb_v" ) in
          mkConstU (new_ax ,EInstance.empty)
          (* raise (GenEx "update_environment: term to translate must be Defined and/or Transparent") *)
        | _ -> raise (GenEx "update_environment: term to translate must be Defined and/or Transparent")
      in
      mk_write_v cake_name cake_val cake_env_constant

  | _ -> raise (GenEx "update_environment: not supported")

let update_environment ref =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  let curr_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !curr_env_name) in

  let new_env = mk_updated_environment ref (mkConstU (curr_env_cname, EInstance.empty)) in (* need something different here *)

  prev_env_name := !curr_env_name;
  curr_env_name := String.concat "" ["cake_env"; string_of_int !next_env_num];
  next_env_num := !next_env_num + 1;

  let _ = Declare.declare_definition
            ~info:(Declare.Info.make ())
            ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string !curr_env_name) ~typ:(Some (TypeGen.sem_env_type (TypeGen.val_type ()))) ())
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
        let prev_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !prev_env_name) in
        create_certificate_theorem global_env (mkConstU (prev_env_cname, EInstance.empty)) (EConstr.of_constr const)

      | Undef _ ->
        let prev_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !prev_env_name) in
        create_axiom_cert_thm global_env (mkConstU (prev_env_cname, EInstance.empty)) const_name (EConstr.of_constr x.const_type)

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

let is_type_synonym r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  match glob_ref with
  | ConstRef const_name ->
    let const_body = Environ.lookup_constant const_name global_env in
    begin
      match const_body.const_body with
      | Def const ->
        if is_type global_env (EConstr.of_constr const) then
          true
        else
          false
      | _ -> false
    end
  | _ -> false

let generate_val_decl_certificate_theorem ~pm ~ref =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let open TypeGen in
  let string_type = string_type () in
  let val_type = val_type () in
  let nat_type = nat_type () in
  let stamp_type = stamp_type () in

  let st = mkApp (get_constant "cake.state_update_next_type_stamp", [| nat_type ; mk_init_st (); int_to_coq_nat !curr_st_num|]) in
  let st' = mkApp (get_constant "cake.state_update_next_type_stamp", [| nat_type ; mk_init_st (); int_to_coq_nat !curr_st_num|]) in

  let prev_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !prev_env_name) in
  let env = mkConstU (prev_env_cname, EInstance.empty) in (* need diff thing here *)

  let curr_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !curr_env_name) in
  let curr_env = mkConstU (curr_env_cname, EInstance.empty) in (* need diff thing here *)

  let default_val =
    mkApp (mk_Litv (),
           [| mkApp (mk_StrLit (), [| str_to_coq_str "FAILURE: hd default" |]) |]) in
  let default_name =
    mkApp (mk_Short (), [| string_type; string_type; str_to_coq_str "default"|]) in
  let default_prod =
    pair_to_coq_pair (default_name, default_val) (ident_type string_type string_type) val_type in
  let env' =
    mkApp (get_constructor "cake.Build_sem_env",
           [| val_type
            ; if is_type_synonym ref then
                mkApp (mk_nsEmpty (), [| string_type; string_type; val_type |])
              else
                list_to_coq_list [mkApp (get_constant "core.list.hd",
                                         [| prod_type (ident_type string_type string_type) val_type;
                                            default_prod;
                                            mkApp (get_constant "cake.sev",
                                                   [| val_type; curr_env |]) |])] (* new thing here *)
                  (prod_type (ident_str_type ()) val_type)
            ; mkApp (mk_nsEmpty (), [| string_type; string_type; prod_type nat_type stamp_type |]) |])
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

let generate_type_decl_certificate_theorem ~pm ~ref =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let open TypeGen in
  let string_type = string_type () in
  let val_type = val_type () in
  let nat_type = nat_type () in
  let stamp_type = stamp_type () in

  let st = mkApp (get_constant "cake.state_update_next_type_stamp", [| nat_type; mk_init_st (); int_to_coq_nat (!curr_st_num - 1)|]) in
  let st' = mkApp (get_constant "cake.state_update_next_type_stamp", [| nat_type ; mk_init_st (); int_to_coq_nat !curr_st_num|]) in

  let prev_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !prev_env_name) in
  let env = mkConstU (prev_env_cname, EInstance.empty) in (* need diff thing here *)

  let curr_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !curr_env_name) in
  let curr_env = mkConstU (curr_env_cname, EInstance.empty) in (* need diff thing here *)

  let glob_ref = locate_global_ref ref in
  let num_constrs = match glob_ref with
    | IndRef (mut_name,index) ->
      let mut_ind_body = Environ.lookup_mind mut_name global_env in
      mut_ind_body.mind_packets.(index).mind_consnames |> Array.length
    | _ -> 0
  in

  let env' =
    mkApp (get_constructor "cake.Build_sem_env",
           [| val_type
            ; mkApp (mk_nsEmpty (), [| string_type; string_type; val_type |])
            ; mkApp (get_constant "core.list.firstn",
                     [| prod_type (ident_type string_type string_type) (prod_type nat_type stamp_type)
                      ; int_to_coq_nat num_constrs
                      ; mkApp (get_constant "cake.sec",
                               [| val_type; curr_env |]) (* here *)
                     |])
           |])
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

let is_type_declaration ~ref =
  let glob_ref = locate_global_ref ref in
  match glob_ref with
  | IndRef _  -> true
  | _ -> false

let generate_decl_certificate_theorem ~pm ~ref =
  let glob_ref = locate_global_ref ref in
  match glob_ref with
  | IndRef _ -> generate_type_decl_certificate_theorem ~pm ~ref
  | ConstRef _ -> generate_val_decl_certificate_theorem ~pm ~ref
  | _ -> failwith "generate_decl_certificate_theorem: not an inductive or constant reference"


let generate_program_decl_certificate_theorem ~pm prog_name =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let decl_constant = get_constant "cake.DECL" in
  let rev_constant = get_constant "core.list.rev" in

  let curr_env_cname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string !curr_env_name) in
  let curr_env = mkConstU (curr_env_cname, EInstance.empty) in (* need diff thing here *)


  let certificate = mkApp (decl_constant,
                           [| mk_init_st (); mk_empty_sem_env ();
                              mkApp (rev_constant, [| TypeGen.dec_type (); !current_program |]);
                              mkApp (get_constant "cake.state_update_next_type_stamp", [|TypeGen.nat_type (); mk_init_st (); int_to_coq_nat !curr_st_num|]);
                              curr_env |]) (* *)
  in

  let certificate_theorem_name = Nameops.add_prefix "cake_prog_" (Nameops.add_suffix (Names.Id.of_string prog_name) "_certificate_thm") in

  let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

  let open Declare in
  let pm = OblState.empty in
  let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
  let info = Info.make () in
  pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'
