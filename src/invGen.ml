open Extraction
open EConstr
open NameManip
open TermGen

exception Unimplemented of string
exception GenEx of string

(* general shape of a refinement invariant *)
(* Given: *)
(*  Inductive type_name (A1 : Type) ... (An : Type) : Type := *)
(*  | C1 : a1 -> ... -> aj -> type_name A1 ... An *)
(*  ... *)
(*  | Cm : b1 -> ... -> bk -> type_name A1 ... An  *)

(* Create: *)
(*  Fixpoint TYPE_NAME (A1 ... An : Type) (AINV1 : A1 -> val -> Prop) ... (AINVn : An -> val -> Prop) (tn : type_name A1 ... An) (v : val) : Prop := *)
(*    match tn with *)
(*    | C1 a1 ... aj -> exists (v1 ... vj : val), v = Conv (TypeStamp (C1, 0), [v1;...;vj]) /\ SOMEINV1 a1 v1 /\ ... /\ SOMEINVj aj vj *)
(*    ... *)
(*    | Cm b1 ... bk -> exists (v1 ... vk : val), v = Conv (TypeStamp (Cm, 0), [v1;...;vj]) /\ SOMEINV1 b1 v1 /\ ... /\ SOMEINVj bj vj *)
   (* where SOMEINVi can be from the AINVs or TYPE_NAME or a previously defined inv *)

(* assumes that name points to a non-mutually recursive type *)
let refinement_invariant env name =
  let open Declarations in
  let mut_body = Environ.lookup_mind name env in
  let is_recursive = mut_body.mind_finite <> BiFinite in
  let one_body = mut_body.mind_packets.(0) in
  let params = mut_body.mind_params_ctxt |> EConstr.of_rel_context in

  let nparams = mut_body.mind_nparams in

  let val_type = TypeGen.val_type () in

  (* TODO: There probably needs to be some check around here in terms of dependent types within the parameters *)
  (* Also needs to address parameters with arrow type. *)
  (* But we currently dont translate inductive types with function arguments so its all good for now *)

  (* For each parameter need to add two arguments to the invariant. One of which is an arbritrary invariant *)
  let arb_inv_type = fun x -> mkArrowR x (mkArrowR val_type mkProp) in

  let invs = List.map (fun decl -> let open Context.Rel.Declaration in
                        let inv_name = Nameops.add_suffix (get_name decl |> id_of_name) "_INV" |> Names.Name.mk_name in
                        LocalAssum (EConstr.annotR inv_name, arb_inv_type (mkRel nparams))) params in

  let params_and_invs = invs @ params in
  let env' = push_rel_context params_and_invs env in
  let sigma = Evd.from_env env' in

  let init_args = fun body -> it_mkLambda_or_LetIn body params_and_invs in

  (* need better checking for non parameterized types *)
  let decreasing_arg_type = Reductionops.beta_applist sigma ((mkIndU ((name,0), EInstance.empty)), (List.init nparams (fun i -> mkRel (2 * nparams - i)))) in
  let decreasing_arg_name = Namegen.hdchar env (Evd.from_env env) decreasing_arg_type |> Names.Id.of_string |> EConstr.annotR in

  let fix_name = Nameops.add_suffix (one_body.mind_typename) "_INV" |> Names.Name.mk_name |> EConstr.annotR in
  let fix_type = mkNamedProd sigma decreasing_arg_name decreasing_arg_type (mkArrowR val_type mkProp) in

  let val_name = Names.Id.of_string "v" |> EConstr.annotR in

  let decreasing_arg_type = Vars.lift 1 decreasing_arg_type in
  let fix_body = fun body -> mkNamedLambda sigma decreasing_arg_name decreasing_arg_type (mkNamedLambda sigma val_name val_type body) in

  let fix = fun body -> mkFix (([| 0 |], 0),
                               ([| fix_name |], [| fix_type |], [| fix_body body |])) in

  let env'' = push_rel (Context.Rel.Declaration.LocalAssum(fix_name,fix_type)) env' in
  let env'' = push_rel (Context.Rel.Declaration.LocalAssum(Context.map_annot Names.Name.mk_name decreasing_arg_name, decreasing_arg_type)) env'' in
  let env'' = push_rel (Context.Rel.Declaration.LocalAssum(Context.map_annot Names.Name.mk_name val_name, val_type)) env'' in
  let sigma = Evd.from_env env'' in

  let offset = if is_recursive then 3 else 2 in (* to be used later in the case that the function is not recursive *)

  let rec mk_type nargs index typ =
    (* Q: What are we doing here? *)
    (* A: moving the variable arguments of a type 'up' with respect to the amount of arguments to some outside function (?) *)
    match kind sigma typ with
    | Rel i -> mkRel (2 * nargs + offset + nparams + i + index - 1)
    | App (hd,args) -> mkApp (mk_type nargs index hd, Array.map (mk_type nargs index) args)
    | Ind _ | Const _ -> typ
    | _ -> raise (GenEx "refinement_invariant: TJ FIX ME PWEAAAAASE")
  in

  let rec mk_inv nargs index typ =
    match kind sigma typ with
    | Rel i -> mkRel (2 * nargs + offset + i - (nargs - index - 1))
    | Ind (typ_name,_) ->
      if Names.Ind.CanOrd.equal typ_name (name,0) then
        mkRel (2 * nargs + offset)
      else
        (* figure out name to use  *)
        (* check if that exists in the current global environment *)
        (* if so then add here else throw exception and say why *)
        let global_env = Global.env () in
        let possible_inv_id = Nameops.add_suffix (Environ.lookup_mind (fst typ_name) global_env).mind_packets.(0).mind_typename "_INV" in
        begin
          try mkConstU ((Nametab.locate_constant (Libnames.qualid_of_ident possible_inv_id)), EInstance.empty)
          with Not_found -> Feedback.msg_info
                              (Pp.str (String.concat "" [(Names.Id.to_string possible_inv_id); " was not found in the current environment."]));
            raise (GenEx "refinement invariant: missing invariant")
        end
    | App (hd,args) ->
      let is_rec =
        if isInd sigma hd then
          let (typ_name,_) = destInd sigma hd in
          Names.Ind.CanOrd.equal typ_name (name,0)
        else false
      in
      let inv = mk_inv nargs index hd in
      let params =
        if is_rec then
          [| |]
        else
          Array.map (mk_type nargs index) args in
      let invs =
        if is_rec then
          [| |]
        else
          Array.map (mk_inv nargs index) args
      in
      mkApp (inv, Array.append params invs)

    | Const (name,univ) ->
      let inv_id = NameManip.constant_inv_name name in
      mkConstU (Libnames.qualid_of_ident inv_id |> Smartlocate.global_constant_with_alias, EInstance.empty)

    | _ ->  raise (Unimplemented "mkinv: funny business, TJ fix ur 'things'")
  in

  let rec combine_invs invs =
    match invs with
    | [] -> raise (UnsupportedFeature "must contain at least one invariant")
    | [x] -> x
    | p :: invs' -> TypeGen.and_type p (combine_invs invs')
  in

  let mk_branch ctxt constr_name =

    let nargs = List.length ctxt - nparams in

    let invs = List.mapi (fun i x ->
        let typ = Context.Rel.Declaration.get_type x in
        let arg = mkRel (i + nargs + 1) in
        let exist = mkRel (i + 1) in
        let inv = mk_inv nargs i typ in
        mkApp (inv, [| arg; exist |]))
      (fst (CList.chop nargs ctxt))
    in

    let lam = fun body -> it_mkLambda_or_LetIn body (CList.chop nargs ctxt |> fst) in

    let existential_vars = List.init nargs (fun i -> mkRel (i + 1)) |> List.rev in
    let rec build_existentials typ index =
      if index = List.length existential_vars then
        fun body -> body
      else
        fun body -> TypeGen.ex_type typ (mkLambda (Names.Id.of_string (String.concat "" ["v"; string_of_int index]) |>
                                                    Names.Name.mk_name |>
                                                    EConstr.annotR, typ, build_existentials typ (index + 1) body))
    in
    let existentials = build_existentials val_type 0 in
    let cake_val =
      let fixed_name = String.capitalize_ascii constr_name |> TermGen.str_to_coq_str in
      let stamp = mkApp (TermGen.mk_TypeStamp (), [| fixed_name; int_to_coq_nat !curr_st_num |]) in
      let stamp_op = TermGen.option_to_coq_option (Some stamp) (TypeGen.stamp_type ()) in

      let args = let _,v = Evarsolve.refresh_universes None env'' sigma val_type in
        TermGen.list_to_coq_list existential_vars v in

      mkApp (TermGen.mk_Conv (),[| stamp_op; args |])
    in

    let equality = TypeGen.eq_type val_type (mkRel (2 * nargs + 1)) cake_val in
    lam (existentials (combine_invs (equality :: List.rev invs)))
  in

  let open Inductiveops in
  let ind_type = make_ind_type (make_ind_family (((name,0), EInstance.empty), Array.init mut_body.mind_nparams (fun i -> EConstr.mkRel (2 * mut_body.mind_nparams - i + offset)) |> Array.to_list), []) in
  let case_info = make_case_info env (name,0) Constr.RegularStyle in (* might switch case style once branches are properly instantiated *) (* lol no *)
  let return =  EConstr.mkLambda (EConstr.anonR, Vars.lift 2 decreasing_arg_type, EConstr.mkProp) in

  let consargs = Array.map fst one_body.mind_nf_lc |> Array.map EConstr.of_rel_context in
  let consnames = one_body.mind_consnames |> Array.map Names.Id.to_string in
  let branches = Array.map2 mk_branch consargs consnames in

  let match_exp = make_case_or_project env (Evd.from_env env) ind_type case_info (return, ERelevance.relevant) (EConstr.mkRel 2) branches in

  let func_hd = fun body -> (init_args (fix body)) in

  if is_recursive then
    func_hd match_exp
  else
    init_args (fix_body match_exp)

(* my naming conventions are uber trash *)

(* Convert Debruijn numbers to named variables when applicable *)
let rec rels_to_vars env typ =
  let open Context.Rel.Declaration in
  let sigma = Evd.from_env env in
  match kind sigma typ with
  (* TODO: if ANON then keep Rel *)
  | Rel i -> lookup_rel i env |> get_name |> id_of_name ~anon:"ANON" |> mkVar
  | Prod (name,typ',body) ->
    let env' = push_rel (LocalAssum (name,typ')) env in
    let typ'' = rels_to_vars env typ' in
    let body' = rels_to_vars env' body in
    mkProd (name,typ'',body')
  | App (hd,args) -> mkApp (rels_to_vars env hd, Array.map (rels_to_vars env) args)
  | Ind _ -> typ
  | Const _ -> typ
  | _ -> PrintDebug.ps "rels_to_vars : not specifically implemented yet"; typ

let rec invariant_from_type env typ =
  let open Context.Rel.Declaration in
  let open Names in
  let sigma = Evd.from_env env in

  let val_type = TypeGen.val_type () in
  (* let eta_typ = Reductionops.shrink_eta sigma typ in *)
  match kind sigma typ with
  (* possible dependent heuristic is if a rel points to something that is NOT a sort *)
  | Rel i ->
    lookup_rel i env |> get_name |>
    id_of_name ~anon:"ANON" |>
    fun id -> Nameops.add_suffix id "_INV" |> mkVar

  | Ind (name,_) ->
    let possible_inv_id = Nameops.add_suffix (Environ.lookup_mind (fst name) (Global.env ())).mind_packets.(0).mind_typename "_INV" in
        begin
          try mkConstU (Nametab.locate_constant (Libnames.qualid_of_ident possible_inv_id), EInstance.empty)
          with Not_found ->
            begin
              Feedback.msg_info
                (Pp.str (String.concat "" [(Names.Id.to_string possible_inv_id); " was not found in the current environment."]));
              raise (GenEx "invariant_from_type: missing invariant")
            end
        end

  | Prod (name,typ',body) ->
    let env' = push_rel (LocalAssum (name,typ')) env in
    let body_inv = invariant_from_type env' body in
    let sigma' = Evd.from_env env' in

    if isArity sigma typ' then
      let inv_id = String.concat "" [TermGen.name_to_str ~anon:"ANON" name.binder_name; "_INV"] |>
                     Id.of_string  in
      let inv_name = Name inv_id in

      let inv_type = mkProd (EConstr.annotR Name.Anonymous,mkRel 1,
                             mkProd (EConstr.annotR Name.Anonymous, val_type, mkProp)) in
      let body_inv' = Vars.subst_var sigma' (id_of_name ~anon:"ANON" name.binder_name) body_inv in
      let body_inv'' = Vars.lift 1 body_inv' in
      let body_inv''' = Vars.subst_var sigma' inv_id body_inv'' in

      mkProd (name, typ', mkProd (EConstr.annotR inv_name, inv_type, body_inv'''))
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

  | Const (constname,univ) ->
    let inv_id = NameManip.constant_inv_name constname in
    mkConstU (Libnames.qualid_of_ident inv_id |> Smartlocate.global_constant_with_alias, EInstance.empty)

  | Lambda _ ->
    let sigma = Evd.from_env env in
    let ctxt,body = EConstr.decompose_lambda sigma typ in

    let env' = EConstr.push_rel_context (List.map (fun (x,y) -> LocalAssum (x,y)) ctxt) env in

    let inv_body = invariant_from_type env' body in

    let arb_inv_type = fun x -> mkArrowR x (mkArrowR val_type mkProp) in

    let param_names = List.map fst ctxt in
    let param_inv_names = List.map (fun name ->
        Context.(name.binder_name) |>
        id_of_name ~anon:"ANON" |>
        (fun id -> Nameops.add_suffix id "_INV") |>
        fun x -> Names.Name.Name x |> EConstr.annotR) param_names
    in

    let param_and_inv_names = List.map (fun x -> Context.(x.binder_name) |> id_of_name) (param_inv_names @ param_names) in
    let inv_body' = Vars.subst_vars sigma param_and_inv_names inv_body in

    let context =
      let len = List.length ctxt in
      (List.map (fun n -> (n, arb_inv_type (mkRel len)) )param_inv_names) @ ctxt
    in
    it_mkLambda inv_body' context

  | Var name -> raise (UnsupportedFeature "invariant_from_type : havent done var")

  | Sort sort -> raise (UnsupportedFeature "invariant_from_type : havent done sort")

  | Case _ -> raise (UnsupportedFeature "invariant_from_type : havent done case")

  | _ -> raise (UnsupportedFeature "invariant_from_type : haven't done yet")

let generate_refinement_invariant r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | IndRef (mutname,index) ->
    if index > 0 then raise (UnsupportedFeature "Mutually Recursive types are not supported");
    if not (Hipattern.is_nodep_ind global_env sigma (mkIndU ((mutname,index), EInstance.empty))) then raise (UnsupportedFeature "Dependent types are not supported");
    let ref_inv = refinement_invariant global_env mutname in
    let sigma',dec_type = Typing.type_of ~refresh:true global_env sigma ref_inv in
    let dec_name = Nameops.add_suffix (Environ.lookup_mind mutname global_env).mind_packets.(0).mind_typename "_INV" in
    let _ = Declare.declare_definition
        ~info:(Declare.Info.make ())
        ~cinfo:(Declare.CInfo.make ~name:dec_name ~typ:(Some dec_type) ())
        ~opaque:false
        ~body: ref_inv
        sigma'
    in
    ()
  | ConstRef name ->
    let body = Global.lookup_constant name in
    let const_type = EConstr.of_constr body.const_type in
    if isArity sigma const_type then
      match body.const_body with
      | Def term ->
        let ref_inv = invariant_from_type global_env (EConstr.of_constr term) in
        let sigma',dec_type = Typing.type_of ~refresh:true global_env sigma ref_inv in
        let dec_name = Nameops.add_suffix (Names.Constant.label name |> Names.Label.to_id) "_INV" in
        let _ = Declare.declare_definition
            ~info:(Declare.Info.make ())
            ~cinfo:(Declare.CInfo.make ~name:dec_name ~typ:(Some dec_type) ())
            ~opaque:false
            ~body: ref_inv
            sigma'
        in
        ()
      | _ -> raise (UnsupportedFeature "only handling defined, transparent references")
    else raise (GenEx "Constant reference must be an arity")
  | _ -> raise (GenEx "Not an inductive type reference")

let print_refinement_invariant r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | IndRef (mutname, index) ->
    if index > 0 then raise (UnsupportedFeature "Mutually Recursive types are not supported");
    let inv_term = refinement_invariant global_env mutname in
    PrintDebug.print_econstr inv_term
  | ConstRef name ->
    let body = Global.lookup_constant name in
    let const_type = EConstr.of_constr body.const_type in
    if isArity sigma const_type then
      match body.const_body with
      | Def term ->
        let inv_term = invariant_from_type global_env (EConstr.of_constr term) in
        PrintDebug.print_econstr inv_term
        | _ -> raise (UnsupportedFeature "only handling defined, transparent references")
    else raise (GenEx "Constant reference must be doing something")
  | _ -> Feedback.msg_info (Pp.str "Not an inductive type reference")
