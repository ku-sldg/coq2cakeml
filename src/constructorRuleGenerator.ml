open InvGen
open EConstr
open TermGen
open TypeGen
open Declarations
open Context.Rel.Declaration

let rec take n l =
  match l with
  | [] -> []
  | x::l' ->
    if n > 0 then
      x::(take (n - 1) l')
    else
      []

let rec drop n l =
  if n <= 0 then l
  else
    begin
      match l with
      | [] -> []
      | _::l' -> drop (n-1) l'
    end

(* Some genius can tell me what combo of map and fold this really is *)
let rec tjs_special_map facb facc c l =
  match l with
  | [] -> []
  | a::l' -> (facb a c)::tjs_special_map facb facc (facc a c) l'

let mk_econ_lemma_from_constructor env one_ind_body cname (* I hate these arguments *) nparams =
  let (typename,index) = cname in
  let index = index - 1 in
  let (args,final_typ) = one_ind_body.mind_nf_lc.(index) in

  let args' = List.rev args |> List.map EConstr.of_rel_decl in (* I don't like this I don't know why its set up like this *)
  let params = take nparams args' in
  let args_no_params = drop nparams args' in

  let env' = push_rel_context params env in
  let arg_invs =
    tjs_special_map
      (fun d e -> invariant_from_type e (get_type d))
      (fun d e -> push_rel (Namegen.name_assumption e (Evd.from_env e) d) e) env' args_no_params
  in

  let arg_names =
    tjs_special_map
      (fun d e -> Namegen.name_assumption e (Evd.from_env e) d)
      (fun d e -> push_rel (Namegen.name_assumption e (Evd.from_env e) d) e) env' args_no_params
  in

  let (env'', arg_names_types) =  Namegen.make_all_rel_context_name_different env' (Evd.from_env env') arg_names in

  let arg_vars = List.map (fun x -> mkVar (NameManip.id_of_name (get_name x))) arg_names_types in
  let arg_exp_names = List.init (List.length arg_vars) (fun i -> Names.Id.of_string (String.concat "" ["e"; string_of_int i])) in
  let arg_exps = List.map mkVar arg_exp_names in

  (* EVAL env e1 (PARAM0_INV a) -> *)
   let arg_EVALs = List.map (fun ((e,inv),t)-> mkEVAL (mkVar (Names.Id.of_string "env")) e (mkApp (inv, [|t|])))
       (List.combine (List.combine arg_exps arg_invs) arg_vars)
  in

  (*  EVAL env (ECon (Some (Short "Cons")) [e1; e2]) (list_INV A A_INV (a::l)). *)

  let final_inv = InvGen.invariant_from_type (EConstr.push_rel_context (EConstr.of_rel_context args) env) (EConstr.of_constr final_typ) in
  let param_names = List.map (fun x -> get_name x |> NameManip.id_of_name |> mkVar) params in
  let cons_term = if List.length args > 0 then
      mkApp (mkConstructU (cname, EInstance.empty), Array.of_list (List.concat [param_names; arg_vars]))
    else
      mkConstructU (cname, EInstance.empty)
  in
  let cake_const_name = NameManip.cakeml_constructor_string (Names.Id.to_string (one_ind_body.mind_consnames.(index)))  in
  let cake_cons_term = mkApp (get_exp_constr "ECon",
                              [| option_to_coq_option (Some (ident_of_str cake_const_name)) (ident_str_type ());
                                 list_to_coq_list arg_exps (exp_type ) |])
  in

  let conclusion = mkEVAL (mkVar (Names.Id.of_string "env")) cake_cons_term (mkApp (final_inv, [| cons_term |])) in

  (* nsLookup ident_string_beq (Short "Cons") (sec env) = Some (2, TypeStamp "Cons" 0) -> *)

  let left_half = mkApp (get_constant "cake.nsLookup",
                              [| string_type; string_type; prod_type nat_type stamp_type;
                                 get_constant "cake.ident_string_beq";
                                 ident_of_str cake_const_name;
                                 mkApp (get_constant "cake.sec", [| val_type; mkVar (Names.Id.of_string "env") |]) |])
  in

  let right_half = option_to_coq_option (Some (pair_to_coq_pair (int_to_coq_nat (List.length args_no_params), mkApp (get_constructor "cake.typestamp",
                                                                                          [| str_to_coq_str cake_const_name;
                                                                                             int_to_coq_nat (!curr_st_num - 1) |]))
                                                 nat_type stamp_type))
                     (prod_type nat_type stamp_type)
  in

  let nsLookup_assum = mk_eq (option_type (prod_type nat_type stamp_type )) left_half right_half in


  (* now we put them all together *)

  let final_prop = List.fold_right mkArrowR (nsLookup_assum::arg_EVALs) conclusion in

  (* add foralls and substitute *)

  (*   forall env PARAM0 PARAM0_INV (e1 e2 : exp) a l, *)
  (* forall A ... Z A_INV ... Z_INV (or A A_INV ... Z Z_INV) env e1 .. en arg1 ... argn *)
  (* env *)

  (* let rec subst_and_add_prod sigma l term = *)
  (*   match l with *)
  (*   | [] -> term *)
  (*   | x::l' -> *)
  (*     let id = get_name x |> NameManip.id_of_name in *)
  (*     mkProd (get_annot x, Context.Rel.Declaration.get_type x, subst_and_add_prod' sigma l' (Vars.subst_var sigma id term)) *)
  (* in *)

  let rec subst_and_add_prod sigma l term =
    match l with
    | [] -> term
    | x::l' ->
      let id = get_name x |> NameManip.id_of_name in
      subst_and_add_prod sigma l' (mkProd (get_annot x, Context.Rel.Declaration.get_type x, Vars.subst_var sigma id term))
  in

  let arb_inv_type = fun x -> mkArrowR x (mkArrowR val_type mkProp) in
  (* param *)
  let prod_params = params in
  (* param_inv  *)
  let prod_param_invs = List.map (fun x -> Context.Rel.Declaration.LocalAssum (NameManip.name_string_map (get_name x) (fun s -> String.concat "" [s; "_INV"]) |> annotR,
                                                                               arb_inv_type (mkVar (get_name x |> NameManip.id_of_name)))) params in
  (* env *)
  let prod_env = [Context.Rel.Declaration.LocalAssum (annotR (Names.Name (Names.Id.of_string "env")), sem_env_type val_type)] in
  (* exps *)
  let prod_exps = List.map2 (fun x y -> Context.Rel.Declaration.LocalAssum (Names.Name x |> annotR, y)) arg_exp_names (List.init (List.length arg_exp_names) (fun _ -> exp_type)) in

  (* args *)
  let rec replace_rels_with_vars env typ =
    let sigma = Evd.from_env env in
    match kind sigma typ with
    | Rel i -> mkVar (get_name (lookup_rel i env) |> NameManip.id_of_name)
    | App (hd, args) -> mkApp (replace_rels_with_vars env hd, Array.map (replace_rels_with_vars env) args )
    | Prod (name, typ, body) ->
      let typ' = replace_rels_with_vars env typ in
      mkProd (name, typ', replace_rels_with_vars (push_rel (LocalAssum (name,typ')) env) body)
    | _ -> typ
  in

  let prod_args = tjs_special_map (fun x e -> LocalAssum (get_annot x, replace_rels_with_vars e (get_type x)))
      (fun x e -> push_rel x e)
      env'
      arg_names_types
  in


  let final_theorem = subst_and_add_prod (Evd.from_env env) (List.concat [prod_params; prod_param_invs; prod_env; prod_exps; prod_args] |> List.rev) final_prop in

  final_theorem

let generate_constructor_lemma ~pm ~ref =
  let glob_ref = Extraction.locate_global_ref ref in
  let global_env = Global.env () in
  let sigma = Evd.from_env global_env in
  match glob_ref with
  | ConstructRef ((mutname, ind_index), cindex) ->
    let mut_body = Environ.lookup_mind mutname global_env in
    let one_body = mut_body.mind_packets.(0) in
    let lemma = mk_econ_lemma_from_constructor global_env one_body ((mutname, ind_index), cindex) mut_body.mind_nparams in
    let lemma_name = (Nameops.add_prefix "EVAL_ECon_") one_body.mind_consnames.(cindex-1) in
    let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma lemma in
    let open Declare in
    let pm = OblState.empty in
    let cinfo' = CInfo.make ~name:lemma_name ~typ:lemma () in
    let info = Info.make () in
    pm, Declare.Proof.start ~info ~cinfo:cinfo' sigma'
  | _ -> Feedback.msg_info (Pp.str "Not an inductive type reference"); raise (GenEx "Messed up")
