(* Certificate Theorem Generation *)

open Extraction
open EConstr

let ps s = Feedback.msg_info (Pp.str s)

let func_inv = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "RefineInv.FUNC")
let eval_term = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "RefineInv.EVAL")
let empty_sem_env = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "SemanticsAux.empty_sem_env")
let empty_namespace =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "CakeSem.Namespace.nsEmpty")

let init_state_fun =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.init_st")

let init_state = mkApp (mkConst init_state_fun, [|TypeGen.nat_type; TermGen.get_nat_constr "O" |])

let extend_dec_env =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "CakeSem.SemanticsAux.extend_dec_env")

let eval_decs_wrapper =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper")

let mk_extend_dec_env new_env sem_env =
  mkApp (mkConst extend_dec_env,[|TypeGen.val_type; new_env; sem_env|])

let mk_empty_namespace mType nType vType = mkApp(mkConst empty_namespace,[|mType; nType; vType|])

let add_value_to_sem_env name cake_val sem_env =
  ()
let add_constructor_to_sem_env name cake_constructor sem_env =
  ()

let mkFUNC typ1 typ2 inv1 inv2 = mkApp(mkConst func_inv,[|typ1; typ2; inv1; inv2|])
let mkEVAL cake_env exp inv = mkApp(mkConst eval_term,[|cake_env; exp; inv|])
let mk_empty_sem_env = mkApp(mkConst empty_sem_env,[|TypeGen.val_type|])

let coq_fst sigma pair =
  let hd, args = destApp sigma pair in
  args.(2)

let coq_snd sigma pair =
  let hd, args = destApp sigma pair in
  args.(3)

(* sem_env val*)
let current_cake_env = ref mk_empty_sem_env
let reset_current_cake_env () = current_cake_env := mk_empty_sem_env
let current_cake_st = ref init_state
let reset_current_cake_st () = current_cake_st := init_state
let clear_semantic_environment () = reset_current_cake_env (); reset_current_cake_st ()

let eval_dec decs env =
  let eval_decs_wrapper = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "EvaluateDecsWrapper.eval_decs_wrapper") in
  mkApp (mkConst eval_decs_wrapper, [| init_state; env; TermGen.list_to_coq_list decs TypeGen.dec_type |])

(* Convert Debruijn numbers to named variables when applicable *)
let rec rels_to_vars env typ =
  let open Context.Rel.Declaration in
  let sigma = Evd.from_env env in
  match kind sigma typ with
  (* TODO: if ANON then keep Rel *)
  | Rel i -> lookup_rel i env |> get_name |> InvGen.id_of_name ~anon:"ANON" |> mkVar
  | Prod (name,typ',body) ->
    let env' = push_rel (LocalAssum (name,typ')) env in
    let typ'' = rels_to_vars env typ' in
    let body' = rels_to_vars env' body in
    mkProd (name,typ'',body')
  | App (hd,args) -> mkApp (rels_to_vars env hd, Array.map (rels_to_vars env) args)
  | Ind _ -> typ
  | _ -> ps "rels_to_vars : not specifically implemented yet"; typ

let rec invariant_from_type env typ =
  let open Context.Rel.Declaration in
  let open Names in
  let sigma = Evd.from_env env in
  match kind sigma typ with
  (* possible dependent heuristic is if a rel points to something that is NOT a sort *)
  | Rel i ->
    lookup_rel i env |> get_name |>
    InvGen.id_of_name ~anon:"ANON" |>
    fun id -> Nameops.add_suffix id "_INV" |> mkVar

  | Ind (name,univ) ->
    begin
      try Indmap.find name !InvGen.global_invariant_table with
      | Not_found -> (print_string "Invariant undefined"; raise Not_found)
    end

  | Prod (name,typ',body) ->
    let env' = push_rel (LocalAssum (name,typ')) env in
    let body_inv = invariant_from_type env' body in
    let sigma' = Evd.from_env env' in

    if isArity sigma typ' then
      let inv_id = String.concat "" [TermGen.name_to_str ~anon:"ANON" name.binder_name; "_INV"] |>
                     Id.of_string  in
      let inv_name = Name inv_id in

      let inv_type = mkProd(Context.annotR Name.Anonymous,mkRel 1,
                            mkProd(Context.annotR Name.Anonymous,TypeGen.val_type,mkProp)) in
      let body_inv' = Vars.subst_var sigma' (InvGen.id_of_name ~anon:"ANON" name.binder_name) body_inv in
      let body_inv'' = Vars.lift 1 body_inv' in
      let body_inv''' = Vars.subst_var sigma' inv_id body_inv'' in

      mkProd (name, typ', mkProd (Context.annotR inv_name, inv_type, body_inv'''))
    else
      let vard_type = rels_to_vars env typ' in
      let vard_body = rels_to_vars env' body in
      let sigma' = Evd.from_env env' in
      let prods,decl = decompose_prod sigma' body_inv in
      let prods' = List.map (fun (x,y) -> LocalAssum (x,y)) prods in
      let inv1 = invariant_from_type env typ' in
      it_mkProd_or_LetIn (mkFUNC vard_type vard_body inv1 decl) prods'

  | App (hd,args) ->
    let hd_inv = invariant_from_type env hd in
    let arg_types = Array.map (rels_to_vars env) args in
    let args_inv = Array.map (invariant_from_type env) args in
    mkApp(hd_inv,Array.concat [arg_types; args_inv])

  | Var name -> raise (UnsupportedFeature "invariant_from_type : havent done var")

  | Sort sort -> raise (UnsupportedFeature "invariant_from_type : havent done sort")

  | Lambda _ -> raise (UnsupportedFeature "invariant_from_type : havent done lambda")

  | Case _ -> raise (UnsupportedFeature "invariant_from_type : havent done case")

  | _ -> raise (UnsupportedFeature "invariant_from_type : haven't done yet")

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
  | IndRef (name,_) | ConstructRef ((name,_),_) ->
    InvGen.generate_refinement_invariant ref;
    let cake_dec = translate_declaration ref in
    let _ = add_dec_to_current_program cake_dec in
    let eval_dec_term = eval_dec [cake_dec] !current_cake_env in
    let res = Reductionops.nf_all global_env sigma eval_dec_term in
    current_cake_env := Reductionops.nf_all global_env sigma (mk_extend_dec_env (coq_snd sigma res) !current_cake_env);
    (* PrintDebug.print_econstr !current_cake_env; *)
    current_cake_st := (coq_fst sigma res)
  | ConstRef (constname) -> print_string "certificateGen.generate_invariant_and_update_environment: CONSTREF\n";
    let const_deref = Environ.lookup_constant constname global_env in
    begin
      match const_deref.const_body with
      | Def term ->
        begin match Constr.kind term with
          | Ind (ind_name,_) -> InvGen.generate_refinement_invariant_from_type_name ind_namd
          | Construct ((ind_name,_),_) -> InvGen.generate_refinement_invariant_from_type_name ind_name
          | Const _ -> print_string "constant 2 electric boogaloo"
          | _ -> print_string "generate_invariant_and_update_environment: hella sad"
        end
      | Undef _ -> print_string "Undef\n"
      | OpaqueDef _ -> print_string "Opaque"
      | Primitive _ -> print_string "Primitive"
    end
  | _ -> raise (UnsupportedFeature "must be a reference to constructor or inductive type")

let generate_certificate_theorem ~pm ~ref =
  let glob_ref = locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  let cake_dec = translate_declaration ref in
  let eval_dec_term = eval_dec [cake_dec] !current_cake_env in
    let res = Reductionops.nf_all global_env sigma eval_dec_term in
    let old_cake_env = !current_cake_env in
    let extended_env = mk_extend_dec_env (coq_snd sigma res) !current_cake_env in
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
