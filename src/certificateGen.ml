(* Certificate Theorem Generation *)

open Extraction
open EConstr

let ps s = Feedback.msg_info (Pp.str s)

let func_inv = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "RefineInv.FUNC")
let eval_term = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "RefineInv.EVAL")
let empty_sem_env = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "empty_sem_env")
let empty_namespace =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "CakeSem.Namespace.nsEmpty")

let extend_dec_env =
  Smartlocate.global_constant_with_alias (Libnames.qualid_of_string "CakeSem.SemanticsAux.extend_dec_env")

let mk_extend_dec_env new_env sem_env =
  mkApp(mkConst extend_dec_env,[|TypeGen.val_type (); new_env; sem_env|])

let mk_empty_namespace mType nType vType = mkApp(mkConst empty_namespace,[|mType; nType; vType|])

let add_value_to_sem_env name cake_val sem_env =
  ()
let add_constructor_to_sem_env name cake_constructor sem_env =
  ()

let mkFUNC typ1 typ2 inv1 inv2 = mkApp(mkConst func_inv,[|typ1; typ2; inv1; inv2|])
let mkEVAL cake_env exp inv = mkApp(mkConst eval_term,[|cake_env; exp; inv|])
let mkEmptyEnv = mkApp(mkConst empty_sem_env,[|TypeGen.val_type ()|])

(* sem_env val*)
let current_cake_env = ref mkEmptyEnv

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
    Indmap.find name !InvGen.global_invariant_table

  | Prod (name,typ',body) ->
    let env' = push_rel (LocalAssum (name,typ')) env in
    let body_inv = invariant_from_type env' body in

    if isArity sigma typ' then
      let inv_id = String.concat "" [TermGen.name_to_str ~anon:"ANON" name.binder_name; "_INV"] |>
                     Id.of_string  in
      let inv_name = Name inv_id in

      let inv_type = mkProd(Context.annotR Name.Anonymous,mkRel 1,
                            mkProd(Context.annotR Name.Anonymous,TypeGen.val_type (),mkProp)) in
      let body_inv' = Vars.subst_var (InvGen.id_of_name ~anon:"ANON" name.binder_name) body_inv in
      let body_inv'' = Vars.lift 1 body_inv' in
      let body_inv''' = Vars.subst_var inv_id body_inv'' in

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
  (* working here *)
  let rels = Array.init (List.length prods / 2) (fun x -> mkRel ((x + 1) * 2))
             |> Array.to_list |> List.rev |> Array.of_list in
  let decl' = mkApp (decl, [|mkApp (term, rels)|]) in
  let prods' = List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) prods in
  it_mkProd_or_LetIn (mkEVAL cake_env exp decl') prods'

let generate_certificate_theorem ref =
    let glob_ref = locate_global_ref ref in
    let global_env = Global.env () in
    let sigma = Evd.from_env global_env in
    match glob_ref with
    | ConstRef const_name ->
      let x = Environ.lookup_constant const_name global_env in
      let certificate = begin
        match x.const_body with
        | Def const ->
          create_certificate_theorem global_env !current_cake_env (EConstr.of_constr const)
        | Undef _ -> raise (UnsupportedFeature "Axioms not supported")
        | _ -> raise (UnsupportedFeature "not doing this part right now")
      end in
      let certificate_theorem_name = const_name |> Names.Constant.label |> Names.Label.to_id
                                     |> Nameops.add_prefix "cake_" |> fun x -> Nameops.add_suffix x "_certificate_thm" in
      let sigma', declaration_type = Typing.type_of ~refresh:true global_env sigma certificate in
      let _ = Declare.declare_definition
        ~info:(Declare.Info.make ())
        ~cinfo:(Declare.CInfo.make ~name:certificate_theorem_name ~typ:(Some declaration_type) ())
        ~opaque:false
        ~body:certificate
        sigma'
      in
      PrintDebug.print_econstr certificate
    | _ -> ()
