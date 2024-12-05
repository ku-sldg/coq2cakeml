(* Take a Coq name and output the CakeML version of it *)
(* Like coq/plugins/extraction/extraction.ml extract_term *)

open CErrors
open Util
open EConstr
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
  let sigma = Evd.from_env env in
  let sigma', typ  = Typing.type_of env sigma term in
  isArity sigma' typ

exception UnsupportedFeature of string

let anon_int = ref 0
let next_anon () =
  let res = String.concat "" ["x"; string_of_int !anon_int] in
  anon_int := !anon_int + 1; res

(* CakeML AST must be loaded into the environment argument *)
let rec translate_term env term =
  let sigma = Evd.from_env env in
  match kind sigma term with
  | Rel i ->
    let open Context.Rel.Declaration in
    let name_str = name_to_str (get_name (Environ.lookup_rel i env)) in
    let id = ident_of_str name_str in
    mkApp (get_exp_constr "EVar", [| id |])

  | Var name ->
    let open Context.Named.Declaration in
    let name_str = Names.Id.to_string (get_id (Environ.lookup_named name env)) in
    let id = ident_of_str name_str in
    mkApp (get_exp_constr "EVar", [| id |])

  | Const (name,univs) ->
    let name_str = name |> Names.Constant.label |> Names.Label.to_string in
    let id = ident_of_str name_str in
    mkApp (get_exp_constr "EVar", [| id |])

  | LetIn (name,term,ty,body) ->
    let env' = push_rel (LocalDef (name,term,ty)) env in
    let cake_name =
      match name.binder_name with
      | Anonymous -> get_option_constr "None"
      | Name id -> mkApp (get_option_constr "Some", [| string_type ;
                                                       str_to_coq_str (Names.Id.to_string id) |])
    in
    (* (* Additional logic for let-fix forms *) *)
    (* if isFix term then *)
    (*   mkApp (get_exp_constr "ELetrec", [| cake_name; translate_term env term; translate_term env' body |]) *)
    (* else *)
      mkApp (get_exp_constr "ELet", [| cake_name; translate_term env term; translate_term env' body |])

  | Lambda (name,typ,body) ->
    let open Names in
    let open Name in
    let name' =
      if name.binder_name = Anonymous
      then Context.map_annot (fun _ -> mk_name (Id.of_string (next_anon ()))) name
      else name in

    let env' = push_rel (LocalAssum (name',typ)) env in
    if isSort sigma typ || Reductionops.is_arity env sigma typ  then translate_term env' body
    else let name_str = name_to_str name'.binder_name in
      mkApp (get_exp_constr "EFun", [| str_to_coq_str name_str; translate_term env' body |])

  | Construct _ -> translate_constructor env term [||]

  | App (hd,args) ->
    if isConstruct sigma hd
    then translate_constructor env hd args
    else translate_application env hd args

  | Fix (_,([|name|],[|typ|],[|body|])) ->
    let env' = push_rel (LocalAssum (name,typ)) env in
    translate_fixpoint env' name body None

  | Fix _ -> raise (UnsupportedFeature ("Mutually recursive fixpoints are unsupported."))

  | Case (ci,u,params,p,iv,c,brs) ->

    let (info,_,_,matched_term,branches_as_functions) = expand_case env sigma (destCase sigma term) in
    let extract_branch i =

      (* for each constructor of the type of the matched term,
         1. get the number of non-parameter arguments to that constructor
         2. decompose that many lambdas off the corresponding item in branches as functions
         3. extract the branch with an environment extended by the number of args
         4. construct the final pattern match *)

      let args, term = decompose_lambda_n_assum sigma (info.ci_cstr_nargs.(i)) branches_as_functions.(i) in

      let env' = List.fold_right push_rel
          (* (List.map (fun (n,t) -> Context.Rel.Declaration.LocalAssum (n,t)) args) *)
          args
          env in
      let cake_exp = translate_term env' term in

      let arg_names = List.map (fun x -> Context.Rel.Declaration.get_name x |> name_to_str) args |>
                      List.rev in
      let arg_pats = List.map (fun x -> mkApp (get_pat_constr "Pvar", [|str_to_coq_str x|])) arg_names in
      let constructor_name = Inductive.lookup_mind_specif env info.ci_ind |>
                             snd |>
                             fun x -> x.mind_consnames.(i) in
      let constr_id =
        mkApp (get_option_constr "Some",
               [| ident_type string_type string_type;
                  mkApp (get_ident_constr "Short", [| string_type; string_type;
                                                      constructor_name |>
                                                      Names.Id.to_string |>
                                                      String.capitalize_ascii |>
                                                      str_to_coq_str |])
               |])
      in

      let constructor_pat =
        mkApp (get_pat_constr "Pcon", [|constr_id; list_to_coq_list arg_pats pat_type |]) in
      pair_to_coq_pair (constructor_pat, cake_exp) pat_type exp_type
    in
    mkApp (get_exp_constr "EMat", [| translate_term env matched_term ;
                                     list_to_coq_list (List.init (Array.length branches_as_functions) extract_branch) (prod_type pat_type exp_type)
                                  |])

  | Ind ((name, ci), _) -> raise (UnsupportedFeature ("Cannot extract types as terms"))

  | Meta _ -> raise (UnsupportedFeature ("Meta"))
  | Evar _ -> raise (UnsupportedFeature ("Evar"))
  | Sort _ -> raise (UnsupportedFeature ("Sort"))
  | Cast _ -> raise (UnsupportedFeature ("Cast"))
  | Prod _
  | Proj _
  | CoFix _
  | Int _
  | Float _
  | Array _
  | String _ -> assert false

and translate_constructor env constructor args =
  let sigma = Evd.from_env env in
  let constructor_name = fst (destConstruct sigma constructor) in
  if Inductiveops.constructor_nallargs env constructor_name = Array.length args then
    let one_ind_body = Inductive.lookup_mind_specif env (fst constructor_name) |> snd in
    let cake_id = one_ind_body.mind_consnames.((constructor_name |> snd) - 1) |>
                  Names.Id.to_string |>
                  String.capitalize_ascii |>
                  ident_of_str in

    let args' = args |>
                Array.to_list |>
                List.filter (fun x -> not (is_type env x)) |>
                List.map (translate_term env) in

    mkApp (get_exp_constr "ECon", [| mkApp(get_option_constr "Some", [|ident_str_type; cake_id|]); list_to_coq_list args' exp_type|])

  else
    let constructor = mkConstructU (constructor_name, EInstance.empty) in
    (* let constructor_type = (Typeops.infer env constructor).uj_type in *)
    let sigma',constructor_type = Typing.type_of ~refresh:true env sigma constructor  in
    let eta_expanded_term = Reduction.eta_expand env (EConstr.to_constr sigma constructor) (EConstr.to_constr sigma' constructor_type) in
    let constr_args = Array.map (EConstr.to_constr sigma) args in
    let beta_reduced_term = Reduction.beta_appvect eta_expanded_term constr_args |> EConstr.of_constr in
    translate_term env beta_reduced_term

and translate_application env func args =
  let rec opapp_helper env application_list =
    match application_list with
    (* if all of the arguments of a function are types that are then erased it could be left as a singleton *)
    | [x] -> translate_term env x
    | [a;f] ->
      mkApp (get_exp_constr "EApp",
             [| get_op_constr "Opapp"; list_to_coq_list [translate_term env f; translate_term env a] exp_type |])
    | x::l ->
      mkApp (get_exp_constr "EApp",
             [| get_op_constr "Opapp"; list_to_coq_list [opapp_helper env l; translate_term env x] exp_type |])
    | _ -> assert false
  in

  let args' = args
              |> Array.to_list
              |> List.filter (fun x -> not (is_type env x))
              |> List.cons func
              |> List.rev
  in
  opapp_helper env args'

and translate_fixpoint env fix_name fix_body let_body =
  let sigma = Evd.from_env env in
  match kind sigma fix_body with
  | Lambda (name,typ,body) ->
    let env' = push_rel (LocalAssum (name,typ)) env in
    if isSort sigma typ then translate_fixpoint env' fix_name body let_body
    else
      let fixpoint_name = str_to_coq_str (name_to_str fix_name.binder_name) in
      let var_name = str_to_coq_str (name_to_str name.binder_name) in
      let fixpoint_body = translate_term env' body in
      let fix_var_names = pair_to_coq_pair (fixpoint_name, var_name) string_type string_type in
      let fixpoint_triple = pair_to_coq_pair (fix_var_names, fixpoint_body) (prod_type string_type string_type) (exp_type) in
      let fixpoint_triple_list = list_to_coq_list [fixpoint_triple] (prod_type (prod_type string_type string_type) exp_type) in
      let in_var =
        match let_body with
        | None -> mkApp (get_exp_constr "EVar", [| ident_of_str (name_to_str fix_name.binder_name) |])
        | Some let_body' -> translate_term env' let_body'
      in
      mkApp (get_exp_constr "ELetrec", [| fixpoint_triple_list; in_var |])

  | _ -> assert false

let fix_type_name str =
  let exploded_str = String.explode str in
  let lowercase_str = (List.hd exploded_str |> String.lowercase_ascii) :: (List.tl exploded_str) in
  String.implode @@ lowercase_str

let fix_type_variable_name str =
  let exploded_str = String.explode str in
  let lowercase_str = (List.hd exploded_str |> String.lowercase_ascii) :: (List.tl exploded_str) in
  String.implode @@ "'"::lowercase_str

let rec translate_ast_t env typ =
  let sigma = Evd.from_env env in
  match kind sigma typ with
  | Rel i ->
    let open Context.Rel.Declaration in
    begin
      let name =  Environ.lookup_rel i env |> get_name in
      match name with
      | Anonymous -> assert false
      | Name id ->
        mkApp (get_ast_t_constr "Atvar", [| id |> Names.Id.to_string |> NameManip.cakeml_type_variable_string |> str_to_coq_str |])
    end

  | App (hd, args) ->
    if isInd sigma hd then
      let ((mut_name,type_index),_) = destInd sigma hd in
      let mut_body = Environ.lookup_mind mut_name env in
      let one_body = mut_body.mind_packets.(type_index) in
      let head_str = one_body.mind_typename |> Names.Id.to_string in
      let head = mkApp(get_ident_constr "Short", [| string_type; string_type; str_to_coq_str head_str |]) in

      let type_args = Array.map (translate_ast_t env) args in

      mkApp (get_ast_t_constr "Atapp", [| type_args |> Array.to_list |> (fun x -> list_to_coq_list x ast_t_type);
                                          head |])
    else if isConst sigma hd then
      let (const_name,_) = destConst sigma hd in
      let head_str = NameManip.id_of_constant const_name |> Names.Id.to_string in
      let head = mkApp(get_ident_constr "Short", [| string_type; string_type; str_to_coq_str head_str |]) in
      let type_args = Array.map (translate_ast_t env) args in

      mkApp (get_ast_t_constr "Atapp", [| type_args |> Array.to_list |> (fun x -> list_to_coq_list x ast_t_type);
                                          head |])

    else
      assert false

  | Ind ((mut_name,type_index),_) ->
    let mut_body = Environ.lookup_mind mut_name env in
    let one_body = mut_body.mind_packets.(type_index) in
    let type_name = one_body.mind_typename |> Names.Id.to_string in
    let short_name = mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str type_name |]) in
    mkApp (get_ast_t_constr "Atapp", [| list_to_coq_list [] ast_t_type; short_name |])

  | Const (constname,_) ->
    let const_str = NameManip.id_of_constant constname |> Names.Id.to_string in
    let short_name = mkApp (get_ident_constr "Short", [| string_type; string_type; str_to_coq_str const_str |]) in
    mkApp (get_ast_t_constr "Atapp", [| list_to_coq_list [] ast_t_type; short_name |])

  | Prod (_,_,_) ->
    raise (UnsupportedFeature "Functions as arguments to constructors is unsupported")

  | Sort _ ->
    raise (UnsupportedFeature "Sorts as arguments to constructors is unsupported")

  | _ -> assert false

let translate_constructor_declaration env name ctxt nb_args =
  let coq_name = name |> Names.Id.to_string |> String.capitalize_ascii |> str_to_coq_str in

  let args_list = List.firstn nb_args ctxt in
  let args_list = List.map_i (fun i pt ->
      pt |> Context.Rel.Declaration.get_type |> translate_ast_t (Environ.pop_rel_context i env))
      1 args_list
  in
  let args_list = List.rev args_list in
  pair_to_coq_pair (coq_name, list_to_coq_list args_list ast_t_type)
    string_type (list_type ast_t_type)

let translate_one_body env one_body =
  let open Names in
  let open Declarations in

  let cons_names = Array.to_list one_body.mind_consnames in
  let cons_args = one_body.mind_nf_lc |> Array.to_list |> List.map fst |> List.map EConstr.of_rel_context in
  let cons_nb_args = Array.to_list one_body.mind_consnrealargs in
  let name_arg_nb = List.combine3 cons_names cons_args cons_nb_args in

  let constructors = List.map (fun (name,args,nb) ->
      translate_constructor_declaration (push_rel_context args env) name args nb)
      name_arg_nb
  in

  let list_cake_cons = list_to_coq_list constructors (prod_type string_type (list_type ast_t_type)) in

  let typename = one_body.mind_typename |> Id.to_string |> fix_type_name |> str_to_coq_str in

  let params = List.skipn one_body.mind_nrealargs one_body.mind_arity_ctxt in

  (* if you have a lower case and uppercase version of the same name they will become the same
     and break the system *)
  let params = List.map (fun pt ->
                         pt |> Context.Rel.Declaration.get_name |>
                         name_to_str |>
                         fix_type_variable_name |>
                         str_to_coq_str)
                         params
  in

  let params = list_to_coq_list (List.rev params) string_type in

  let params_name_pair = pair_to_coq_pair (params, typename) (list_type string_type) string_type in
  pair_to_coq_pair (params_name_pair, list_cake_cons)
    (prod_type (list_type string_type) string_type)
    (list_type (prod_type string_type (list_type ast_t_type)))

let translate_type_definition env (mut_body : Declarations.mutual_inductive_body) =
  let open Declarations in
  let mut_rec_types = Array.map (translate_one_body env) mut_body.mind_packets |> Array.to_list in
  if List.length mut_rec_types > 1 then raise (UnsupportedFeature "Mutually recursive types not supported")
  else
    list_to_coq_list mut_rec_types (prod_type
                                      (prod_type (list_type string_type) string_type)
                                      (list_type (prod_type string_type (list_type ast_t_type))))

let unknown_loc = list_to_coq_list [] nat_type

let translate_let_declaration env name term =
  let def_name = mkApp (get_pat_constr "Pvar", [| name |> Names.Constant.label |> Names.Label.to_string |> str_to_coq_str |]) in
  mkApp (get_dec_cons "Dlet", [|unknown_loc; def_name; translate_term env term |])

let translate_type_declaration env mut_body =
  mkApp (get_dec_cons "Dtype", [|unknown_loc; translate_type_definition env mut_body|])

let translate_type_synonym env name term typ =
  let sigma = Evd.from_env env in
  let normalized_term = Reduction.eta_expand env term typ |> EConstr.of_constr in
  let i = Termops.nb_lam sigma normalized_term in
  let (context,end_term) = EConstr.decompose_lambda_n_decls sigma i normalized_term in
  let vars = NameManip.context_to_var_names context |>
             List.map str_to_coq_str |>
             (fun x -> list_to_coq_list x string_type)
  in
  let ast = translate_ast_t (EConstr.push_rel_context context env) end_term in
  mkApp (get_dec_cons "Dtabbrev", [| unknown_loc; vars; name; ast |])

let translate_declaration r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  match glob_ref with
  | ConstRef const_name ->
    let const_body = Environ.lookup_constant const_name global_env in
    begin
      match const_body.const_body with
      | Def const ->
        if is_type global_env (EConstr.of_constr const) then
          let name = NameManip.id_of_constant const_name |>
                     Names.Id.to_string |>
                     NameManip.cakeml_variable_string |>
                     str_to_coq_str
          in
          translate_type_synonym global_env name const const_body.const_type
        else
        begin
          try translate_let_declaration global_env const_name (EConstr.of_constr const) with
          | (UnsupportedFeature error) as err -> (Feedback.msg_info (Pp.str error); raise err)
        end
      | Undef _ -> raise (UnsupportedFeature "Axioms not supported")
      | _ -> Feedback.msg_info (Pp.str "Not a defined constant");
        raise (UnsupportedFeature "translate_declaration: actually an error")
    end

  | IndRef (name,_)  ->
    let mut_body = Environ.lookup_mind name global_env in
    translate_type_declaration global_env mut_body

  | ConstructRef ((name,_),_) ->
    Feedback.msg_info (Pp.str "Not a constant or inductive type: is a constructor reference");
    raise (UnsupportedFeature "translate_declaration: actually an error")

  | VarRef _ ->
    Feedback.msg_info (Pp.str "Not a constant at all: is a Section variable");
    raise (UnsupportedFeature "translate_declaration: actually an error")

let translate_and_print r =
  let dec = translate_declaration r in
  begin
    try print_econstr dec with
    | UnsupportedFeature error -> Feedback.msg_info (Pp.str error)
  end

(* let translate_and_print r = *)
(*   let glob_ref = locate_global_ref r in *)
(*   let global_env = Global.env () in *)
(*   match glob_ref with *)
(*   | ConstRef const_name -> *)
(*     let const_body = Environ.lookup_constant const_name global_env in *)
(*     begin *)
(*       match const_body.const_body with *)
(*       | Def const -> *)
(*         begin *)
(*           try print_econstr (translate_let_declaration global_env const_name (EConstr.of_constr const)) with *)
(*           | UnsupportedFeature error -> Feedback.msg_info (Pp.str error) *)
(*         end *)
(*       | Undef _ -> raise (UnsupportedFeature "Axioms not supported") *)
(*       | _ -> Feedback.msg_info (Pp.str "Not a defined constant") *)
(*    end *)

(*   | IndRef (name,_) | ConstructRef ((name,_),_) -> *)
(*     let mut_body = Environ.lookup_mind name global_env in *)
(*     print_econstr (translate_type_definition global_env mut_body) *)

(*   | VarRef _ -> Feedback.msg_info (Pp.str "Not a constant at all: is a Section variable") *)

let current_program = ref (list_to_coq_list [] dec_type)
let reset_current_program () = current_program := list_to_coq_list [] dec_type

let add_dec_to_current_program dec =
  current_program := mkApp(get_list_constr "cons", [| dec_type; dec; !current_program |])

let translate_and_add_to_global_environment r =
  begin try
      let dec = translate_declaration r in
      let name = String.concat "" ["cake_"; Libnames.string_of_qualid r] in
      let _ = Declare.declare_definition
          ~info:(Declare.Info.make ())
          ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string name) ~typ:(Some dec_type) ())
          ~opaque:false
          ~body:dec
          Evd.empty
      in
      let _ = add_dec_to_current_program dec in
      ()
    with
    | UnsupportedFeature error -> Feedback.msg_info (Pp.str error)
  end

(* let translate_and_add_to_global_environment r = *)
(*   let glob_ref = locate_global_ref r in *)
(*   let global_env = Global.env () in *)
(*   match glob_ref with *)
(*   | ConstRef const_name -> *)
(*     let const_body = Environ.lookup_constant const_name global_env in *)
(*     begin *)
(*       match const_body.const_body with *)
(*       | Def const -> *)
(*         begin *)
(*           try let cake_declaration = translate_let_declaration global_env const_name (EConstr.of_constr const) in *)
(*             let dec_type = get_type "CakeSem.CakeAST" "dec" in *)
(*             let name = String.concat "" ["cake_"; const_name |> Names.Constant.label |> Names.Label.to_string  ] in *)
(*             let _ = Declare.declare_definition *)
(*                                ~info:(Declare.Info.make ()) *)
(*                                ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string name) ~typ:(Some dec_type) ()) *)
(*                                ~opaque:false *)
(*                                ~body:cake_declaration *)
(*                                Evd.empty *)
(*             in *)
(*             let _ = add_dec_to_current_program cake_declaration in *)
(*             () *)

(*           with *)
(*           | UnsupportedFeature error -> Feedback.msg_info (Pp.str error) *)
(*         end *)
(*       | _ -> Feedback.msg_info (Pp.str "Not a defined constant") *)
(*     end *)

(*   | IndRef (name,_) | ConstructRef ((name,_),_) -> *)
(*     begin *)
(*       try *)
(*         let mut_body = Environ.lookup_mind name global_env in *)
(*         let cake_type_def = translate_type_declaration global_env mut_body in *)
(*         let dec_type = get_type "CakeSem.CakeAST" "dec" in *)
(*         let name = String.concat "" ["cake_"; name |> Names.MutInd.label |> Names.Label.to_string  ] in *)
(*         let _ = Declare.declare_definition *)
(*             ~info:(Declare.Info.make ()) *)
(*             ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string name) ~typ:(Some dec_type) ()) *)
(*             ~opaque:false *)
(*             ~body:cake_type_def *)
(*             Evd.empty *)
(*         in *)
(*         let _ = add_dec_to_current_program cake_type_def in *)
(*         () *)
(*       with *)
(*       | UnsupportedFeature error -> Feedback.msg_info (Pp.str error) *)
(*     end *)

(*   | VarRef _ -> Feedback.msg_info (Pp.str "Not a constant at all: is a Section variable") *)
