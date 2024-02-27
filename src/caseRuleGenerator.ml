open EConstr

(* used to calculate what number parameter a specific rel variable within a constructor definition has *)
let rel_to_param arg_index rel num_params num_args =
  num_args + num_params - arg_index - rel - 1

let generate_pat_strs' cargs_no_params =
  let helper curr now = List.init now (fun i -> Names.Id.of_string ("pat_str" ^ (string_of_int (i + curr)))) in
  let rec other_helper curr l =
    match l with
    | [] -> []
    | n::ls -> (helper curr n)::(other_helper (curr+n) ls)
  in
  other_helper 0 cargs_no_params

let generate_pat_strs num_params constructor_args =
  let num_const_args = List.map (fun l -> List.length l - num_params) constructor_args in
  generate_pat_strs' num_const_args

let mk_case_theorem env (inductive_name : Names.inductive) =
  let mut_body = Environ.lookup_mind (fst inductive_name) env in
  if Array.length mut_body.mind_packets > 1 then raise (Extraction.UnsupportedFeature "mk_case_theorem: mutually recursive types not supported");
  let sigma = Evd.from_env env in
  let one_body = mut_body.mind_packets.(0) in


  let open Context.Rel.Declaration in
  let open Names in
  (* let open Univ in *)
  let num_params = mut_body.mind_nparams_rec in
  (* let param_types = mut_body.mind_params_ctxt |> *)
  (*              of_rel_context |> *)
  (*              List.map (fun x -> get_type x) *)
  (* in *)

  (* Setting up all the variable names and their types *)
  let param_name i = Names.Id.of_string ("PARAM" ^ string_of_int i) in
  let param_names = List.init num_params param_name in
  (* let param_type = mkType (Univ.Universe.make (Univ.Level.var 1)) in *)

  let result_name = Names.Id.of_string ("RESULT_TYPE") in
  let max_univ = Univ.Level.Set.choose (UGraph.domain (Environ.universes env)) in
  let result_type = mkType (Univ.Universe.make max_univ) in

  let refinement_invariant_names = List.map (fun name -> Nameops.add_suffix name "_INV") param_names in
  let arb_inv_type = fun x -> mkArrowR x (mkArrowR (TypeGen.val_type) mkProp) in
  let refinement_invariant_types = List.map (fun name -> arb_inv_type (mkVar name)) param_names in

  let result_invariant_name = Names.Id.of_string ("RESULT_INV") in
  let _ = result_invariant_name in
  let result_invariant_type = arb_inv_type (mkVar result_name) in

  let mat = Id.of_string "mat" in
  let num_constructors = Array.length one_body.mind_consnrealdecls in
  let c_names = List.init num_constructors (fun i -> Id.of_string ("c_" ^ string_of_int i)) in

  let rec convert_rel_to_named nargs arg_index typ =
    match kind sigma typ with
    | Rel i -> mkVar (param_name (nargs + num_params - arg_index - i - 1))
    | App (hd,args) -> mkApp (convert_rel_to_named nargs arg_index hd, Array.map (convert_rel_to_named nargs arg_index) args)
    | Ind (name,_) -> typ
    | Const _ -> typ
    | Prod _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Prod not implemented")
    | Lambda _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Lambda not implemented")
    | LetIn _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: LetIn not implemented")
    | Var _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Var not implemented")
    | Construct _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Constructor not implemented")
    | Case _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Case not implemented")
    | Fix _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Case not implemented")
    | CoFix _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Case not implemented")
    | Sort _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: Sort not implemented")
    | _ -> raise (Extraction.UnsupportedFeature "convert_rel_to_named: TJ FIX ME PWEAAAAASE")
  in

  let ctor_to_function_type ctor =
    (* [argn;...;arg1;PARAMm;...PARAM1] *)
    let nargs = List.length ctor - num_params in
    (* [argn;...;arg1] *)
    let args,_ = Util.List.chop nargs ctor in
    Util.List.fold_left_i (fun i rhs next ->
        mkArrowR (convert_rel_to_named nargs i next) rhs)
      0 (mkVar (result_name))
      args
  in

  let b_names = List.init num_constructors (fun i -> Id.of_string ("b_" ^ string_of_int i)) in
  let b_types = one_body.mind_nf_lc |>
                Array.map fst |>
                Array.map of_rel_context |>
                Array.map (List.map get_type) |>
                Array.map ctor_to_function_type |>
                Array.to_list
  in

  let matched_name = Id.of_string "matched" in
  let matched_type = mkApp (mkInd inductive_name, List.map mkVar param_names |> Array.of_list) in

  let orig_name = Id.of_string "orig" in
  (* let orig_type = mkVar result_name in *)

  let pat_str_names = generate_pat_strs num_params (Array.map fst one_body.mind_nf_lc |> Array.to_list) in

  let env_name = Id.of_string "env" in
  (* let env_type = TypeGen.sem_env_type TypeGen.val_type in *)


  (*  orig = match matched with *)
  (*         | C_1 => b_1 *)
  (*         | C_2 A_1 .. A_n => b_2 A_1 .. A_n *)
  (*         | C_3 A_1 .. A_m => b_3 A_1 .. A_m *)
  (*         | C_4 A_1 .. A_q => b_4 A_1 .. A_q *)
  (*             .. *)
  (*         end -> *)

  let open Inductiveops in
  (* problem somewhere, probably need to add lambdas in front of the b's *)
  let case_info = make_case_info env inductive_name Sorts.Relevant Constr.RegularStyle in
  let ind_fam = make_ind_family (Univ.in_punivs inductive_name, List.map Constr.mkVar param_names) in
  let ind_type = make_ind_type (ind_fam,[]) in
  let cases = List.map2 (fun b typ -> Reduction.eta_expand env b typ) (List.map (to_constr sigma) (List.map mkVar b_names)) (List.map (to_constr sigma) b_types) in
  let return = mkLambda (Context.annotR Names.Anonymous, matched_type, mkVar result_name) in
  let match_statement = make_case_or_project env sigma ind_type case_info return (mkVar matched_name) (List.map of_constr cases |> Array.of_list) in

  let equiv_prop = TypeGen.eq_type (mkVar result_name) (mkVar orig_name) match_statement in

  (* good_cons_env  [(Pcon (Some (Short "CakeConsName1") []), c_1) *)
  (*                 (Pcon (Some (Short "CakeConsName2") [Pvar pat_str_1; .. Pvar pat_str_n]), c_2) *)
  (*                 .. *)
  (*                 (Pcon (Some (Short "CakeConsNamer") [Pvar pat_str_1; .. Pvar pat_str_m]), c_r) ] *)
  (*               env (TypeStamp "" ??) -> *)
  let con_to_cake_pat constructor_name pat_strs c =
    let open TermGen in
    let open TypeGen in
    let pcon = get_pat_constr "Pcon" in
    let pvar = get_pat_constr "Pvar" in
    let fixed_constructor_name = Id.to_string constructor_name |> String.capitalize_ascii in

    let pats = List.map (fun p -> mkApp (pvar, [|p|])) pat_strs in
    let option_name = mkApp (get_option_constr "Some", [| ident_type string_type string_type;
                                                          mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str fixed_constructor_name |]) |])
    in
    let const_pat = mkApp (pcon, [| option_name; list_to_coq_list pats pat_type |]) in

    pair_to_coq_pair (const_pat,c) pat_type exp_type
  in

  let trips = List.combine
      (List.combine (Array.to_list one_body.mind_consnames) (List.map (List.map mkVar) pat_str_names))
      (List.map mkVar c_names)
  in

  let cake_list_pats = TermGen.list_to_coq_list
      (List.map (fun ((n,ps),c) -> con_to_cake_pat n ps c) trips)
      TypeGen.(prod_type pat_type exp_type)
  in

  let type_stamp = mkApp (TermGen.get_stamp_constr "TypeStamp", [| TermGen.str_to_coq_str ""; TermGen.get_nat_constr "O" |]) in
  let good_cons_env_prop = mkApp (TermGen.mk_good_cons_env, [| cake_list_pats; mkVar env_name; type_stamp |]) in

  let eval_term = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "RefineInv.EVAL") in
  let mkEVAL cake_env exp inv = mkApp(mkConst eval_term,[|cake_env; exp; inv|]) in

  let inv_id = Nameops.add_suffix (Environ.lookup_mind (fst inductive_name) (Global.env ())).mind_packets.(0).mind_typename "_INV" in
  let inv_const =
    try mkConst (Nametab.locate_constant (Libnames.qualid_of_ident inv_id))
    with Not_found -> raise (InvGen.GenEx (String.concat "" [Names.Id.to_string inv_id; " is not defined in the current environment"]))
  in
  let eval_prop = mkEVAL (mkVar env_name) (mkVar mat)
      (mkApp (inv_const,
              List.append (List.append param_names refinement_invariant_names) [matched_name] |>
              Array.of_list |>
              Array.map mkVar ))
  in

  (* now we need a function to generate each "sub goal" per constructor *)

  (* (forall a_1 .. a_n v_1 .. v_n, x = Cr a_1 .. a_n -> *)
  (*  a_1_INV a_1 v1 -> ... -> a_n_INV a_n v_n -> *)
  (*  EVAL (extend_dec_env (Build_sem_env (nsBind pat_str_n v_n (nsBind pat_str_n-1 v_n-1 (... (nsBind pat_str_1 v_1)) nsEmpty))) env)) c_r (res_INV (b_r a_1 .. a_n)) -> *)

  let create_hyp_for_constructor index =
    let constructor_args = fst one_body.mind_nf_lc.(index) in
    let num_constructor_args = List.length constructor_args - num_params in
    let (constructor_args,_) = Util.List.chop num_constructor_args constructor_args in

    let generate_name base i = Nameops.add_suffix (Id.of_string (base ^ "_")) (string_of_int i) in
    let arg_names = List.init num_constructor_args (generate_name "a") in
    let arg_types = List.map (fun x -> get_type x |> of_constr) constructor_args |>
                    List.mapi (fun i t -> convert_rel_to_named num_constructor_args i t) |>
                    List.rev
    in
    let val_names = List.init num_constructor_args (generate_name "v") in

    (* there is a special place in hell for people who mix index by 0 and index by 1 in the same project *)
    let match_eq_prop = TypeGen.eq_type matched_type (mkVar matched_name)
        (mkApp (mkConstruct (inductive_name,index+1), List.append param_names arg_names |>
        List.map mkVar |>
        Array.of_list))
    in

    let rec mk_inv typ arg_index =
      match kind sigma typ with
      | Rel i -> mkVar (Id.of_string ("PARAM" ^ (string_of_int (rel_to_param arg_index i num_constructor_args num_params)) ^ "_INV"))
      | Ind (ind_name,_) ->
        let inv_id = Nameops.add_suffix (Environ.lookup_mind (fst ind_name) (Global.env ())).mind_packets.(0).mind_typename "_INV" in
        begin
          try mkConst (Nametab.locate_constant (Libnames.qualid_of_ident inv_id))
          with Not_found -> raise (InvGen.GenEx (String.concat "" [Names.Id.to_string inv_id; " was not found in the current environment"]))
        end
      | App (hd,args) -> mkApp (mk_inv hd arg_index, Array.append (Array.map (convert_rel_to_named num_constructor_args arg_index) args) (Array.map (fun t -> mk_inv t arg_index) args) )

      | Const (const_name,_) ->
        let inv_id = NameManip.constant_inv_name const_name in
        begin
          try mkConst (Nametab.locate_constant (Libnames.qualid_of_ident inv_id))
          with Not_found -> raise (InvGen.GenEx (String.concat "" [Names.Id.to_string inv_id; " was not found in the current environment"]))
        end

      | _ -> raise (InvGen.GenEx "messed up or an error: unclear yet")
    in

    let constructor_args,_ =  Util.List.chop num_constructor_args constructor_args in

    let arg_invs = List.mapi (fun i t -> mk_inv (of_constr (get_type t)) i) constructor_args |> List.rev in

    let applied_invs = List.map (fun (inv,(a,v)) -> mkApp (inv, [|mkVar a; mkVar v|])) (List.combine arg_invs (List.combine arg_names val_names)) in

    let open TermGen in
    let open TypeGen in

    let pat_strs = List.nth pat_str_names index in

    let pat_val_pairs = List.combine pat_strs val_names in

    let nsEmpty_sev = mkApp (mk_nsEmpty, [| string_type; string_type; val_type|]) in
    let nsEmpty_sec = mkApp (mk_nsEmpty, [| string_type; string_type; prod_type nat_type stamp_type|]) in
    let nsBind_list = List.fold_left (fun x (p,v) -> mkApp (TermGen.mk_nsBind, [|string_type; string_type; val_type; mkVar p; mkVar v; x|]) ) nsEmpty_sev pat_val_pairs in

    let updated_env = mkApp (mk_extend_dec_env, [| val_type;
                                                   mkApp (mk_Build_sem_env, [|val_type; nsBind_list; nsEmpty_sec|]);
                                                   mkVar env_name |]) in

    let eval_prop = TermGen.mkEVAL updated_env (mkVar (List.nth c_names index)) (mkApp (mkVar result_invariant_name, [|mkApp (mkVar (List.nth b_names index), Array.of_list arg_names |> Array.map mkVar)|] )) in

    let full_prop_var = mkArrowR match_eq_prop
        (List.fold_right mkArrowR applied_invs eval_prop)
    in

    let full_prop_rel = Vars.subst_vars sigma (List.append arg_names val_names |> List.rev) full_prop_var in

    let full_prop_vals = it_mkProd full_prop_rel (List.map (fun n -> (Context.annotR (Names.Name.Name n), val_type)) val_names |> List.rev) in

    it_mkProd full_prop_vals (List.map (fun (n,t) -> (Context.annotR (Names.Name.Name n), t)) (List.combine arg_names arg_types) |> List.rev)

  in

  let constructor_hyps = List.init (List.length c_names) create_hyp_for_constructor in

  (* Conclusion *)
  (* EVAL env (EMat mat [(Pcon (Some (Short "CakeConsName1") []), c_1) *)
  (*                       (Pcon (Some (Short "CakeConsName2") [Pvar pat_str_1; .. Pvar pat_str_n]), c_2) *)
  (*                       .. *)
  (*                       (Pcon (Some (Short "CakeConsNamer") [Pvar pat_str_1; .. Pvar pat_str_m]), c_r) ] *)
  (*             (res_INV orig) *)

  let conc_prop = mkEVAL (mkVar env_name) (mkApp (TermGen.get_exp_constr "EMat", [| mkVar mat; cake_list_pats |])) (mkApp (mkVar result_invariant_name, [|mkVar orig_name|])) in

  (* Putting all the propositions together *)

  let final_prop = List.fold_right mkArrowR (equiv_prop::good_cons_env_prop::eval_prop::constructor_hyps) conc_prop in

  (* All final substitutions *)
  let env_subst = Vars.subst_var sigma env_name final_prop in
  let env_prod = mkProd (Context.annotR (Name.Name env_name), TypeGen.sem_env_type TypeGen.val_type, env_subst) in

  let all_pats = List.flatten pat_str_names in
  let pat_str_subst = Vars.subst_vars sigma (List.rev all_pats) env_prod in
  let pat_str_prod = it_mkProd pat_str_subst (List.combine (List.map (fun id -> Name.Name id |> Context.annotR) all_pats) (List.init (List.length all_pats) (fun _ -> TypeGen.string_type)) |> List.rev) in

  let orig_subst = Vars.subst_var sigma orig_name pat_str_prod in
  let orig_prod = mkProd (Name orig_name |> Context.annotR, mkVar result_name, orig_subst) in

  let matched_subst = Vars.subst_var sigma matched_name orig_prod in
  let matched_prod = mkProd (Name matched_name |> Context.annotR, matched_type, matched_subst) in

  let b_subst = Vars.subst_vars sigma (List.rev b_names) matched_prod in
  let b_prod = it_mkProd b_subst (List.combine (List.map (fun id -> Name.Name id |> Context.annotR) b_names) b_types |> List.rev) in

  let mat_c_names = mat::c_names in
  let c_mat_subst = Vars.subst_vars sigma (List.rev (mat_c_names)) b_prod in
  let c_mat_prod = it_mkProd c_mat_subst (List.combine (List.map (fun id -> Name.Name id |> Context.annotR) mat_c_names) (List.init (List.length mat_c_names) (fun _ -> TypeGen.exp_type)) |> List.rev) in

  let res_inv_subst = Vars.subst_var sigma result_invariant_name c_mat_prod in
  let res_inv_prod = mkProd (Name result_invariant_name |> Context.annotR, result_invariant_type, res_inv_subst) in

  let param_invs_subst = Vars.subst_vars sigma (List.rev refinement_invariant_names) res_inv_prod in
  let param_invs_prod = it_mkProd param_invs_subst (List.combine (List.map (fun id -> Name id |> Context.annotR) refinement_invariant_names) refinement_invariant_types |> List.rev) in

  let result_and_params = List.append param_names [result_name] in
  let param_result_subst = Vars.subst_vars sigma (List.rev result_and_params) param_invs_prod in
  let param_result_prod = it_mkProd param_result_subst
      (List.combine (List.map (fun id -> Name id |> Context.annotR) result_and_params)
         (List.init (List.length result_and_params) (fun _ -> result_type)) |> List.rev) in

  param_result_prod


let generate_match_theorem ~pm ~ref =
  let glob_ref = Extraction.locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | IndRef (name,_) | ConstructRef ((name,_),_) ->
    let case_theorem = mk_case_theorem global_env (name,0) in
    let theorem_name = Nameops.add_prefix "EVAL_EMat_" (Environ.lookup_mind name global_env).mind_packets.(0).mind_typename in
    let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma case_theorem in
    let open Declare in
    let pm = OblState.empty in
    let cinfo' = CInfo.make ~name:theorem_name ~typ:case_theorem () in
    let info = Info.make () in
    pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'

  | _ -> raise (Extraction.UnsupportedFeature "must be a reference to constructor or inductive type")
