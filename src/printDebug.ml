(* Debugging functions *)
let print_constr ?(debruijn = false) ?(env = Global.env ()) e =
  let sigma = Evd.from_env env in
  let env' = if debruijn then Environ.pop_rel_context (Environ.nb_rel env) env
             else env in

  Feedback.msg_info (Ppconstr.pr_constr_expr env' sigma
                       (Constrextern.extern_constr env' sigma (EConstr.of_constr e)))

let print_arity arity =
  let open Declarations in
  let open Sorts in
  let do_thing sort =
    let sort_str = if is_prop sort then "Prop"
      else if is_set sort then "Set"
      else if is_sprop sort then "SProp"
      else if is_small sort then "Type (Small)"
      else "Type (Probably)"
    in
    let sort_rel =
      match relevance_of_sort sort with
      | Relevant -> "Relevant"
      | Irrelevant -> "Irrelevant"
    in
    print_endline ("RELEVANCE: " ^ sort_rel);
    print_endline ("THE SORT IS: " ^ sort_str);
  in
  match arity with
  | RegularArity a ->
    print_endline "RegularArity: ";
    do_thing a.mind_sort;
    print_string "THE CONSTRUCTION IS: ";
    print_constr a.mind_user_arity

  | TemplateArity b ->
    print_endline "TemplateArity: ";
    do_thing (sort_of_univ b.template_level);
    print_endline ""

let print_unsafe_type env c =
  let uj = Typeops.infer env c in
  print_endline "Unsafe Type Judgement: ";
  print_string "\tVal:  "; print_constr uj.uj_val;
  print_string "\tType: "; print_constr uj.uj_type

let print_name n =
  let open Names.Name in
  match n with
  | Anonymous -> print_string "Anonymous"
  | Name n -> print_string (Names.Id.to_string n)

let print_pt ?env pt =
  let open Context.Rel.Declaration in
  match pt with
  | LocalAssum (n,t) -> print_name n.binder_name; print_string " : "; print_constr ?env t
  | LocalDef (n,c,t) -> print_name n.binder_name; print_string " = ";
                        print_constr ?env c; print_string "    : ";
                        print_constr ?env t

let rec print_env_rel ?(debruijn = false) (env : Environ.env) =
  if env.env_nb_rel = 0 then ()
  else
    let pt = Environ.lookup_rel 1 env in
    let env' = Environ.pop_rel_context 1 env in
    let env'' = if debruijn then Environ.pop_rel_context (Environ.nb_rel env) env
      else env' in
    print_pt ~env:env'' pt;
    print_env_rel ~debruijn:debruijn env'
