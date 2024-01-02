(* Certificate Theorem Generation *)

open Extraction
open EConstr
open InvGen
open CakeEnv
open TermGen

let eval_dec decs env =
  let eval_decs_wrapper = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper") in
  mkApp (mkConst eval_decs_wrapper, [| init_state; env; TermGen.list_to_coq_list decs TypeGen.dec_type |])

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
let create_decl_certificate_theorem start_st start_env =
  let decl_constant = mkConst (Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "DECL")) in
  let rev_constant = mkConst (Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "rev")) in
  mkApp (decl_constant,
         [| start_st; start_env;
            mkApp (rev_constant, [| TypeGen.dec_type; !current_program |]);
            !current_cake_st; !current_cake_env |])

let generate_invariant_and_update_environment ref =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | IndRef _ ->
    InvGen.generate_refinement_invariant ref;
    let cake_dec = translate_declaration ref in
    let _ = add_dec_to_current_program cake_dec in
    let eval_dec_term = eval_dec [cake_dec] !current_cake_env in
    let res = Reductionops.nf_all global_env sigma eval_dec_term in
    current_cake_env := Reductionops.nf_all global_env sigma (apply_extend_dec_env (coq_snd sigma res) !current_cake_env);
    current_cake_st := (coq_fst sigma res)

  | ConstRef _ ->
    InvGen.generate_refinement_invariant ref;
    let cake_dec = translate_declaration ref in
    let _ = add_dec_to_current_program cake_dec in
    let eval_dec_term = eval_dec [cake_dec] !current_cake_env in
    let res = Reductionops.nf_all global_env sigma eval_dec_term in
    current_cake_env := Reductionops.nf_all global_env sigma (apply_extend_dec_env (coq_snd sigma res) !current_cake_env);
    current_cake_st := (coq_fst sigma res)

  | _ -> raise (UnsupportedFeature "must be a reference to an inductive type")

let generate_certificate_theorem ~pm ~ref =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  let cake_dec = translate_declaration ref in
  let eval_dec_term = eval_dec [cake_dec] !current_cake_env in
    let res = Reductionops.nf_all global_env sigma eval_dec_term in
    let old_cake_env = !current_cake_env in
    let extended_env = apply_extend_dec_env (coq_snd sigma res) !current_cake_env in
    (* PrintDebug.print_econstr extended_env; *)
    let _ = add_dec_to_current_program cake_dec in
    current_cake_env := Reductionops.nf_all global_env sigma extended_env;
    match glob_ref with
    | ConstRef const_name ->
      let x = Environ.lookup_constant const_name global_env in
      let certificate = begin
        match x.const_body with
        | Def const ->
          create_certificate_theorem global_env old_cake_env (EConstr.of_constr const);
        | Undef _ -> raise (UnsupportedFeature "Axioms not supported")
        | _ -> raise (UnsupportedFeature "not doing this part right now")
      end in
      let certificate_theorem_name =
        const_name |> Names.Constant.label |> Names.Label.to_id
        |> Nameops.add_prefix "cake_" |> fun x -> Nameops.add_suffix x "_certificate_thm" in
      let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

      let open Declare in
      let pm = OblState.empty in
      (* let sigma'', evar =  Evarutil.new_evar global_env sigma' certificate in *)
      (* let cinfo = CInfo.make ~name:certificate_theorem_name ~typ:(EConstr.to_constr sigma'' certificate) () in *)
      let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
      let info = Info.make () in
      (* let obls_info,_,term,_ = RetrieveObl.retrieve_obligations global_env certificate_theorem_name sigma'' 0 evar certificate in *)
      (* let pm,prog = Obls.add_definition ~pm ~cinfo ~term ~info ~uctx:(Evd.evar_universe_context sigma'') ~opaque:false obls_info in *)
      pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'

    (* | IndRef (mut_name,_) | ConstructRef ((mut_name,_),_) -> *)
    | _ -> raise (UnsupportedFeature "need to come back here")

let generate_decl_certificate_theorem ~pm prog_name =
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in

  let certificate = create_decl_certificate_theorem init_state (mkApp (mkConst empty_sem_env, [| TypeGen.val_type |])) in
  let certificate_theorem_name = Nameops.add_prefix "cake_prog_" (Nameops.add_suffix (Names.Id.of_string prog_name) "_certificate_thm") in

  let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in

  let open Declare in
  let pm = OblState.empty in
  let cinfo' = CInfo.make ~name:certificate_theorem_name ~typ:certificate () in
  let info = Info.make () in
  pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'
