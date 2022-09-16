(* Take a Coq name and output the CakeML version of it *)
(* Like coq/plugins/extraction/extraction.ml extract_term *)

open CErrors
open Util
open Constr
open TypeGen
open TermGen
open PrintDebug

let locate_global_ref qid =
  let ro =
    try Some (Smartlocate.global_with_alias qid)
    with Nametab.GlobalizationError _ | UserError _ -> None
  in
  match ro with
    | None -> Nametab.error_global_not_found ~info:Exninfo.null qid
    | Some r -> r

let is_type env term =
  let uj = Typeops.infer env term in
  Constr.isSort uj.uj_type

(* CakeML AST must be loaded into the environment argument *)
let rec extract_term env c =
  match Constr.kind c with
  | Rel i ->
    begin
      match Environ.lookup_rel i env with
      | LocalDef (name,_,_) | LocalAssum (name,_) ->
        let name_str = name_to_str name in
        let id = ident_of_str name_str in
        mkApp (get_exp_constr "EVar", [| id |])
    end

  | Var n ->
    (match Environ.lookup_named n env with | LocalDef (name,_,_) | LocalAssum (name,_) ->
       let name_str =  Names.Id.to_string name.binder_name in
       let id = ident_of_str name_str in
       mkApp (get_exp_constr "EVar", [| id |]))

  | Meta _ -> assert false
  | Evar _ -> assert false
  | Sort _ -> assert false

  | Cast _ -> assert false
  | Prod (a,b,c) -> assert false

  | Lambda (name,typ,body) ->
    let env' = Environ.push_rel (LocalAssum (name,typ)) env in
    if isSort typ then extract_term env' body
    else let name_str = name_to_str name in
      mkApp (get_exp_constr "EFun", [| str_to_coq_str name_str; extract_term env' body |])

  | LetIn (name,term,ty,body) ->
    let open Names in
    let env' = Environ.push_rel (LocalDef (name,term,ty)) env in
    let name_op =
      match name.binder_name with
      | Anonymous -> get_option_constr "None"
      | Name id -> mkApp (get_option_constr "Some", [| string_type ; str_to_coq_str (Id.to_string id) |])
    in
    mkApp (get_exp_constr "ELet", [| name_op; extract_term env term; extract_term env' body |])

  | App (hd,args) -> extract_app env hd args

  | Const (n,u) ->
    let name_str = Names.Constant.to_string n in
    let id = ident_of_str name_str in
    mkApp (get_exp_constr "EVar", [| id |])

  | Ind ((name, ci), _) ->
    print_endline "Hit a type as term";
    get_exp_constr "EHandle"

  | Construct (((tn,ti), ci), _) -> extract_constructor env c [| |]

  | Case (ci,u,params,p,iv,c,brs) ->
    (* Extremely Naive Here *)
    let mkPvar name =
      let name_str = name_to_str name in
      mkApp (get_pat_constr "Pvar", [| str_to_coq_str name_str |])
    in

    let extract_patterns one_ind_bdy branches =
      let open Declarations in
      let branches = Array.to_list branches in
      let consnames = Array.to_list one_ind_bdy.mind_consnames in
      List.map (fun ((vars,_), cons_name) ->
          let cons_name = Names.Id.to_string cons_name in
          let id = ident_of_str cons_name in
          let constr_id = mkApp (get_option_constr "Some", [| ident_str_type; id |]) in

          let vars = vars |> Array.to_list |> List.map mkPvar in
          let coq_list_pat_vars = list_to_coq_list vars pat_type in

          mkApp (get_pat_constr "Pcon", [| constr_id; coq_list_pat_vars |]))
        (List.combine branches consnames)
    in

    let extract_branches one_ind_bdy branches =
      let open Declarations in
      let branches = Array.to_list branches in
      let params = Array.to_list params in
      let cons_types = Array.to_list (one_ind_bdy.mind_user_lc) in

      let cons_types = List.map (fun typ -> Reduction.hnf_prod_applist env typ params
                       |> Term.decompose_prod
                       |> fst)
          cons_types in
      let cons_types = List.map (fun name_type_list ->
          List.map (fun (name,typ) -> Context.Rel.Declaration.LocalAssum(name,typ)) name_type_list)
          cons_types in

      List.map (fun (ctxt, (vars,term)) ->
          let env' = Environ.push_rel_context ctxt env in
          extract_term env' term) (List.combine cons_types branches)
    in

    let one_bdy = (Environ.lookup_mind (fst ci.ci_ind) env).mind_packets.(snd ci.ci_ind) in

    let pat_br_lst = List.combine (extract_patterns one_bdy brs) (extract_branches one_bdy brs) in
    let pat_br_lst = List.map (fun x ->
        pair_to_coq_pair x pat_type exp_type)
        pat_br_lst
    in
    let coq_pat_exp_list = list_to_coq_list pat_br_lst (prod_type pat_type exp_type) in
    let discriminee = extract_term env c in

    mkApp (get_exp_constr "EMat", [| discriminee; coq_pat_exp_list |])

  | Fix  ((is,i), (names,types,bodies)) ->
    let names = Array.to_list names in
    let types = Array.to_list types in
    let bodies = Array.to_list bodies in

    if List.length names <> List.length bodies || List.length names <> List.length types
    then assert false
    else
      let func_names = List.map name_to_str names in
      let func_var_bodies = List.map (fun x -> match Constr.kind x with
          | Lambda (name,typ,body) ->
            let context = List.map (fun x ->
                Context.Rel.Declaration.LocalAssum (fst x, snd x))
                (List.combine names types) in
            let env' = List.fold_left (fun e r -> Environ.push_rel r e) env context in
            let env'' = Environ.push_rel (LocalAssum (name,typ)) env' in
            (str_to_coq_str (name_to_str name), extract_term env'' body)
          | _ -> assert false)
          bodies in
      let name_var_bodies = List.map (fun (f,(v,b)) ->
          pair_to_coq_pair (pair_to_coq_pair (str_to_coq_str f,v) string_type string_type, b)
            (prod_type string_type string_type) exp_type)
          (List.combine func_names func_var_bodies) in
      let nvb_coq =
        list_to_coq_list  name_var_bodies (prod_type (prod_type string_type string_type) exp_type) in
      let in_var = mkApp (get_exp_constr "EVar", [| ident_of_str (List.nth func_names i)|]) in

      mkApp (get_exp_constr "ELetrec", [| nvb_coq; in_var |])

  | Proj (n,b) -> assert false
  | CoFix _ -> assert false
  | Int _   -> assert false
  | Float _ -> assert false
  | Array _ -> assert false

and extract_app env c args =
  match Constr.kind c with
  | Construct _ -> extract_constructor env c args
  | _ -> opapp_app_list env (c::Array.to_list args)

and extract_constructor env cons args =
  let (((tn,ti), ci), u)= Constr.destConstruct cons in (* Throws DestKO exception if not a Construct *)

  let mut_bdy = Environ.lookup_mind tn env in
  let one_bdy = mut_bdy.mind_packets.(ti) in

  let is_eq_args =  mut_bdy.mind_nparams + one_bdy.mind_consnrealargs.(ci-1) = Array.length args in
  let cons_type = (Typeops.infer env cons).uj_type in
  if not is_eq_args
  then let eta = (Reduction.eta_expand env cons cons_type) in
       let beta = Reduction.beta_appvect eta args in
       extract_term env (Constr.mkApp (beta,args))
  else
  (* filter out any argument that is a type *)

  let name_str = Names.Id.to_string mut_bdy.mind_packets.(ti).mind_consnames.(ci-1) in
  let id = ident_of_str name_str in
  let constr_id = mkApp (get_option_constr "Some", [| ident_str_type; id |]) in

  let args' = Array.of_list (List.filter (fun x -> x |> is_type env |> not) (Array.to_list args)) in
  let const_args = list_to_coq_list (List.map (extract_term env) (Array.to_list args')) exp_type in
  mkApp (get_exp_constr "ECon", [| constr_id; const_args |])

and opapp_app_list env constr_list =
  let rec opapp_helper env constr_list =
    match constr_list with
    | [a;f] ->
      mkApp (get_exp_constr "EApp",
             [| get_op_constr "Opapp"; list_to_coq_list [extract_term env f; extract_term env a] exp_type |])
    | x::l ->
      mkApp (get_exp_constr "EApp",
             [| get_op_constr "Opapp"; list_to_coq_list [opapp_helper env l ; extract_term env x] exp_type |])
    | _ -> assert false
  in
  let types_removed_list = (List.hd constr_list) :: List.filter (fun term -> term |> is_type env |> not) (List.tl constr_list) in
  (* match types_removed_list with *)
  (* | [term] -> extract_term env term *)
  (* | _ -> *) opapp_helper env (List.rev types_removed_list)

(* Currently this will make the type incorrect if: *)
(* - there is another parameter with the same name that already starts with a lowercase *)
(* - there are invalid chars in the parameter (idk what these are r.n.) *)
let fix_name str =
  let exploded_str = String.explode str in
  let lowercase_str = (List.hd exploded_str |> String.lowercase_ascii) :: (List.tl exploded_str) in
  String.implode @@ "'"::lowercase_str

let rec extract_ast_t env typ =
  match Constr.kind typ with
  | Rel i ->
    let open Context.Rel.Declaration in
    begin
      match Environ.lookup_rel i env with
      | LocalAssum (binder,_) | LocalDef (binder,_,_) ->
        let name = binder.binder_name in
        match name with
        | Anonymous -> assert false
        | Name id ->

          mkApp (get_ast_t_constr "Atvar", [| id |> Names.Id.to_string |> fix_name |> str_to_coq_str |])
    end

  | App (typ, args) -> extract_ast_t_app env typ args

  | Ind ((name,tid),u) -> extract_ast_t_app env typ [||]

  | _ -> assert false

and extract_ast_t_app env term args =
  match Constr.kind term with
  | Ind ((name,tid),u) ->
    let mut_body = Environ.lookup_mind name env in
    let one_body = mut_body.mind_packets.(tid) in
    let typename = one_body.mind_typename in

    let args = Array.map (extract_ast_t env) args in
    let args = Array.to_list args in
    mkApp (get_ast_t_constr "Atapp",
           [| list_to_coq_list args ast_t_type; typename |> Names.Id.to_string |> ident_of_str |])

  | _ -> assert false

let extract_ind_constructor env name (ctxt : rel_context) nb_args =
  let coq_name = name |> Names.Id.to_string |> str_to_coq_str in

  let args_list = List.firstn nb_args ctxt in
  let args_list = List.map_i (fun i pt ->
      pt |> Context.Rel.Declaration.get_type |> extract_ast_t (Environ.pop_rel_context i env))
      1 args_list
  in
  let args_list = List.rev args_list in
  pair_to_coq_pair (coq_name, list_to_coq_list args_list ast_t_type)
    string_type (list_type ast_t_type)

let extract_one_body env one_body =
  let open Names in
  let open Declarations in

  let to_list = Array.to_list in
  let cons_names = to_list one_body.mind_consnames in
  let cons_args = one_body.mind_nf_lc |> to_list |> List.map fst in
  let cons_nb_args = to_list one_body.mind_consnrealargs in
  let name_arg_nb = List.combine cons_names (List.combine cons_args cons_nb_args) in

  let constructors = List.map (fun (name,(args,nb)) ->
      extract_ind_constructor (Environ.push_rel_context args env) name args nb)
      name_arg_nb
  in

  let list_cake_cons = list_to_coq_list constructors (prod_type string_type (list_type ast_t_type)) in

  let typename = one_body.mind_typename |> Id.to_string |> str_to_coq_str in

  let params = List.skipn one_body.mind_nrealargs one_body.mind_arity_ctxt in
  let params = List.map (fun pt ->
      pt |> Context.Rel.Declaration.get_annot |> name_to_str |> fix_name |> str_to_coq_str)
      params
  in

  let params = list_to_coq_list (List.rev params) string_type in

  let params_name_pair = pair_to_coq_pair (params, typename) (list_type string_type) string_type in
  pair_to_coq_pair (params_name_pair, list_cake_cons)
    (prod_type (list_type string_type) string_type)
    (list_type ast_t_type)

let extract_inductive env (mut_body : Declarations.mutual_inductive_body) =
  let open Declarations in

  let mut_rec_types = Array.map (extract_one_body env) mut_body.mind_packets |> Array.to_list in
  list_to_coq_list mut_rec_types (prod_type
                                    (prod_type (list_type string_type) string_type)
                                    (list_type (prod_type string_type (list_type ast_t_type))))

let locs = list_to_coq_list [] nat_type

let extract_inductive_declaration env mut_body =
  mkApp (get_dec_cons "Dtype", [| locs; extract_inductive env mut_body |])

let extract_var_declaration env name term =
  let def_name = mkApp (get_pat_constr "Pvar", [| name |> Names.Constant.to_string |> str_to_coq_str |]) in
  mkApp (get_dec_cons "Dlet", [| def_name; extract_term env term |])

let rec extract_function_declaration env func_name lambda =
  match kind lambda with
  | Lambda (var_name,typ,body) ->
    let env' = Environ.push_rel (LocalAssum (var_name,typ)) env in

    if Reductionops.is_sort env Evd.empty (EConstr.of_constr typ) || Reduction.is_arity env typ
    then extract_function_declaration env' func_name body
    else
      let f_v_name_pair = pair_to_coq_pair (func_name |> Names.Constant.to_string |> str_to_coq_str,
                                            var_name |> name_to_str |> str_to_coq_str)
                                            string_type string_type in
      let trip = pair_to_coq_pair (f_v_name_pair, extract_term env' body)
                                  (prod_type string_type string_type)
                                  (exp_type) in
      let trip_list = list_to_coq_list [trip] (prod_type (prod_type string_type string_type) exp_type) in

      mkApp (get_dec_cons "Dletrec", [| locs; trip_list |])

  | _ -> extract_var_declaration env func_name lambda

let extract_declaration env const_name const_body =
  let open Declarations in
  match const_body with
  | Def const -> extract_function_declaration env const_name const
  | _ -> assert false

let simple_extraction r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  match glob_ref with
  | ConstRef const_name ->
    let const_body = Environ.lookup_constant const_name global_env in
    begin match const_body.const_body with
      | Def const ->
        print_constr (extract_declaration global_env const_name const_body.const_body)
      | _ -> Feedback.msg_info (Pp.str "not a defined constant")
    end

  | IndRef (name,_) | ConstructRef ((name,_),_) ->
    let mut_body = Environ.lookup_mind name global_env in
    print_constr (extract_inductive_declaration global_env mut_body)

  | VarRef _ -> Feedback.msg_info (Pp.str "not a constant at all: is a variable")
