open Extraction

exception Unimplemented of string
exception GenEx of string

let global_invariant_table : Constr.t Names.Indmap.t ref = ref Names.Indmap.empty

(* Should be in a different place *)
let id_of_name ?(anon="x") n =
  let open Names in
  match n with
  | Anonymous -> Id.of_string anon
  | Name id -> id

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
  let one_body = mut_body.mind_packets.(0) in
  let params = mut_body.mind_params_ctxt in

  let nparams = mut_body.mind_nparams in

  (* TODO: There probably needs to be some check around here in terms of dependent types within the parameters *)
  (* Also needs to address parameters with arrow type *)

  (* For each parameter need to add two arguments to the invariant. One of which is an arbritrary invariant *)
  let arb_inv_type = fun x -> Term.mkArrowR x (Term.mkArrowR (TypeGen.val_type ()) Constr.mkProp) in

  let invs = List.map (fun decl -> let open Context.Rel.Declaration in
                        let inv_name = Nameops.add_suffix (get_name decl |> id_of_name) "_INV" |> Names.Name.mk_name in
                        LocalAssum (Context.annotR inv_name, arb_inv_type (Constr.mkRel nparams))) params in

  let params_and_invs = invs @ params in

  let init_args = fun body -> Term.it_mkLambda_or_LetIn body params_and_invs in

  (* need better checking for non parameterized types *)
  let decreasing_arg_type = Reduction.beta_appvect (Constr.mkInd (name,0)) (Array.init nparams (fun i -> Constr.mkRel (2 * nparams - i))) in
  let decreasing_arg_name = Namegen.hdchar env (Evd.from_env env) (EConstr.of_constr decreasing_arg_type) |> Names.Id.of_string |> Context.annotR in

  let fix_name = Nameops.add_suffix (one_body.mind_typename) "_INV" |> Names.Name.mk_name |> Context.annotR in
  let fix_type = Term.mkNamedProd decreasing_arg_name decreasing_arg_type (Term.mkArrowR (TypeGen.val_type ()) Constr.mkProp) in

  let val_name = Names.Id.of_string "v" |> Context.annotR in

  let decreasing_arg_type = Constr.lift 1 decreasing_arg_type in
  let fix_body = fun body -> Term.mkNamedLambda decreasing_arg_name decreasing_arg_type (Term.mkNamedLambda val_name (TypeGen.val_type ()) body) in

  let fix = fun body -> Constr.mkFix (([| 0 |], 0),
                                      ([| fix_name |], [| fix_type |], [| fix_body body |])) in

  let offset = 3 in (* to be used later in the case that the function is not recursive *)

  let rec mk_type nargs index typ =
    let open Constr in
    match kind typ with
    | Rel i -> mkRel (2 * nargs + offset + nparams + i - index - 1)
    | App (hd,args) -> mkApp (mk_type nargs index hd, Array.map (mk_type nargs index) args)
    | Ind (name,_) -> typ
    | _ -> raise (UnsupportedFeature "TJ FIX ME PWEAAAAASE")
  in

  let rec mk_inv nargs index typ =
    let open Constr in
    match kind typ with
    | Rel i -> mkRel (2 * nargs + offset + i - (nargs - index - 1))
    | Ind (typ_name,_) ->
      if Names.Ind.CanOrd.equal typ_name (name,0) then
        mkRel (2 * nargs + offset)
      else Names.Indmap.find typ_name !global_invariant_table
    | App (hd,args) ->
      let is_rec =
        if isInd hd then
          let (typ_name,_) = destInd hd in
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
    | _ -> raise (Unimplemented "mkbranch: funny business, TJ fix ur shit")
  in

  let rec combine_invs invs =
    match invs with
    | [] -> raise (UnsupportedFeature "must contain at least one invariant")
    | [x] -> x
    | p :: invs' -> TypeGen.and_type p (combine_invs invs')
  in

  let mk_branch ctxt constr_name =
    let open Constr in

    let nargs = List.length ctxt - nparams in

    let invs = List.mapi (fun i x ->
        let typ = Context.Rel.Declaration.get_type x in
        let arg = mkRel (i + nargs + 1) in
        let exist = mkRel (i + 1) in
        let inv = mk_inv nargs i typ in
        mkApp (inv, [| arg; exist |]))
      (fst (CList.chop nargs ctxt))
    in

    let lam = fun body -> Term.it_mkLambda_or_LetIn body (CList.chop nargs ctxt |> fst) in

    let existential_vars = List.init nargs (fun i -> mkRel (i + 1)) |> List.rev in
    let rec build_existentials typ index =
      if index = List.length existential_vars then
        fun body -> body
      else
        fun body -> TypeGen.ex_type typ (mkLambda (Names.Id.of_string (String.concat "" ["v"; string_of_int index]) |>
                                                    Names.Name.mk_name |>
                                                    Context.annotR, typ, build_existentials typ (index + 1) body))
    in
    let existentials = build_existentials (TypeGen.val_type ()) 0 in
    let cake_val =
      let fixed_name = String.capitalize_ascii constr_name |> TermGen.str_to_coq_str in
      let stamp = Constr.mkApp (TermGen.get_stamp_constr "TypeStamp", [| fixed_name; TermGen.get_nat_constr "O" |]) in (* Here we're always giving the typestamp 0, might need to change later *)
      let stamp_op = TermGen.option_to_coq_option (Some stamp) TypeGen.stamp_type in


      let args = TermGen.list_to_coq_list existential_vars (TypeGen.val_type ()) in

      Constr.mkApp (TermGen.get_val_constr "Conv",[|stamp_op; args|])
    in

    let equality = TypeGen.eq_type (TypeGen.val_type ()) (Constr.mkRel (2 * nargs + 1)) cake_val in
    lam (existentials (combine_invs (equality :: List.rev invs)))
  in

  let open Inductiveops in
  let ind_type = make_ind_type (make_ind_family (Univ.in_punivs (name,0), Array.init mut_body.mind_nparams (fun i -> Constr.mkRel (2 * mut_body.mind_nparams - i + offset)) |> Array.to_list), []) in
  let case_info = make_case_info env (name,0) Sorts.Relevant Constr.RegularStyle in (* might switch case style once branches are properly instantiated *)
  let return =  EConstr.mkLambda (Context.anonR, decreasing_arg_type |> Constr.lift 2 |>  EConstr.of_constr, EConstr.mkProp) in
  let branches = Array.map2 (fun x -> fst x |> mk_branch) one_body.mind_nf_lc (one_body.mind_consnames |> Array.map Names.Id.to_string) |> Array.map (EConstr.of_constr) in

  let match_exp = make_case_or_project env (Evd.from_env env) ind_type case_info return (EConstr.mkRel 2) branches in



  let func_hd = fun body -> (init_args (fix body)) in

  func_hd (EConstr.to_constr (Evd.from_env env) match_exp)



(* adds invariant to the global invariant table as a side effect *)
(* let register_refinement_inv (name : Names.inductive) (inv : Constr.t) = *)

let generate_refinement_invariant r =
  let glob_ref = locate_global_ref r in
  let global_env = Global.env () in
  match glob_ref with
  | IndRef (name, index) ->
    if index > 0 then raise (UnsupportedFeature "Mutually Recursive types are not supported")
    else let ref_inv = refinement_invariant global_env name in
      (* Feedback.msg_info (Constr.debug_print ref_inv); *)
      PrintDebug.print_constr ref_inv;
      let _ = print_endline "INFERING" in
      let judgement = Typeops.infer_type global_env ref_inv in
      let _ = print_endline "END INFERENCE" in
      let dec_type = judgement.utj_val in
      let _ = print_endline "HERE" in
      let dec_name = Nameops.add_suffix (Environ.lookup_mind name global_env).mind_packets.(0).mind_typename "_INV" in
      let _ = print_endline "HERE2" in
      let invariant_glob_ref = Declare.declare_definition
        ~info:(Declare.Info.make ())
        ~cinfo:(Declare.CInfo.make ~name:dec_name ~typ:(Some (EConstr.of_constr dec_type)) ())
        ~opaque:false
        ~body:(EConstr.of_constr ref_inv)
        Evd.empty
      in
      let _ = print_endline "HERE3" in
      let constant_ref =
        let open Globnames in
        if isConstRef invariant_glob_ref then
          Constr.mkConst (destConstRef invariant_glob_ref)
        else
          raise (GenEx "Not a constant reference")
      in
      global_invariant_table := Names.Indmap.add (name,0) constant_ref !global_invariant_table
      (* register_refinement_invariant ref_inv *)

  | _ -> Feedback.msg_info (Pp.str "Not an inductive type: is a Section variable")
