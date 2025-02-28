(* Debugging functions *)
let name_to_string n =
  match n with
  | Names.Name id -> Names.Id.to_string id
  | Names.Anonymous -> "_"

let rec print_constr_shape c =
  match Constr.kind c with
  | Rel i -> "(Rel " ^ string_of_int i ^ ")"
  | Var n -> String.concat "" ["(Var : "; Names.Id.to_string n; ")"]
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod (n,t,c') when n.binder_name = Names.Anonymous -> String.concat "" ["(";print_constr_shape t;") -> "; print_constr_shape c']
  | Prod (n,t,c') -> String.concat "" ["!(";name_to_string n.binder_name; " : "; print_constr_shape t;")."; print_constr_shape c']
  | Lambda (_,_,c') -> String.concat "" ["\\. "; "("; print_constr_shape c'; ")"]
  | LetIn (_,c1,_,c2) -> String.concat "" ["let ("; print_constr_shape c1; ") in ("; print_constr_shape c2; ")" ]
  | App (hd,args) -> String.concat "" ["("; String.concat " " (List.map print_constr_shape (hd :: Array.to_list args)); ")"]
  | Case (_,_,_,_,_,c',cs) ->
    String.concat "" ["case "; print_constr_shape c'; " of " ; Array.map snd cs |> Array.to_list |> List.map print_constr_shape |> String.concat " |->" ]
  | Const (n,_) -> String.concat "" ["(Const : "; Names.Constant.to_string n; ")"]
  | Ind ((n,i),_) -> String.concat "" ["(Ind : "; Names.Id.to_string (Environ.lookup_mind n (Global.env ())).mind_packets.(i).mind_typename; ")"]
  | Construct (((n,i),ci),_) -> String.concat "" ["(Construct : "; Names.Id.to_string ((Environ.lookup_mind n (Global.env ())).mind_packets.(i)).mind_consnames.(0); ")"]
  | Fix ((_,i),(_,_,cs))-> String.concat "" ["f\\. ("; print_constr_shape cs.(i); ")"]
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | Int _ | Float _ | Array _ | String _ -> "Builtin"

let rec print_econstr_shape c =
  match EConstr.kind (Evd.from_env (Global.env ())) c with
  | Rel i -> "(Rel " ^ string_of_int i ^ ")"
  | Var n -> String.concat "" ["(Var : "; Names.Id.to_string n; ")"]
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod (n,t,c') when n.binder_name = Names.Anonymous -> String.concat "" ["(";print_econstr_shape t;") -> "; print_econstr_shape c']
  | Prod (n,t,c') -> String.concat "" ["!(";name_to_string n.binder_name; " : "; print_econstr_shape t;")."; print_econstr_shape c']
  | Lambda (_,_,c') -> String.concat "" ["\\. "; "("; print_econstr_shape c'; ")"]
  | LetIn (_,c1,_,c2) -> String.concat "" ["let ("; print_econstr_shape c1; ") in ("; print_econstr_shape c2; ")" ]
  | App (hd,args) -> String.concat "" ["("; String.concat " " (List.map print_econstr_shape (hd :: Array.to_list args)); ")"]
  | Case (_,_,_,_,_,c',cs) ->
    String.concat "" ["case "; print_econstr_shape c'; " of " ; Array.map snd cs |> Array.to_list |> List.map print_econstr_shape |> String.concat " |->" ]
  | Const (n,_) -> String.concat "" ["(Const : "; Names.Constant.to_string n; ")"]
  | Ind ((n,i),_) -> String.concat "" ["(Ind : "; Names.Id.to_string (Environ.lookup_mind n (Global.env ())).mind_packets.(i).mind_typename; ")"]
  | Construct (((n,i),ci),_) -> String.concat "" ["(Construct : "; Names.Id.to_string ((Environ.lookup_mind n (Global.env ())).mind_packets.(i)).mind_consnames.(ci - 1); ")"]
  | Fix ((_,i),(_,_,cs))-> String.concat "" ["f\\. ("; print_econstr_shape cs.(i); ")"]
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | Int _ | Float _ | Array _ | String _ -> "Builtin"

let print_constr ?(debruijn = false) ?(env = Global.env ()) e =
  let sigma = Evd.from_env env in
  let env' = if debruijn then Environ.pop_rel_context (Environ.nb_rel env) env
             else env in

  (* debuggin sesh*)
  let ofc = EConstr.of_constr e in
  let ast = (Constrextern.extern_constr env' sigma ofc) in
  let msg = Ppconstr.pr_constr_expr env' sigma ast in
  (* END debuggin sesh*)

  Feedback.msg_info msg

let print_econstr ?(debruijn = false) ?(env = Global.env ()) e =
  let sigma = Evd.from_env env in
  let env' = if debruijn then Environ.pop_rel_context (Environ.nb_rel env) env
    else env in

  (* debuggin sesh*)
  let _,_ = Typing.type_of env' sigma e in
  let ast = (Constrextern.extern_constr env' sigma e) in
  let msg = Ppconstr.pr_constr_expr env' sigma ast in
  (* END debuggin sesh*)

  Feedback.msg_info msg

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
      | RelevanceVar _ -> "RelevanceVar"
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
    do_thing (b.template_level);
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
  | LocalAssum (n,t) -> print_name n.binder_name; print_string " : "; print_econstr ?env t
  | LocalDef (n,c,t) -> print_name n.binder_name; print_string " = ";
                        print_econstr ?env c; print_string "    : ";
                        print_econstr ?env t

let rec print_pt_list env pts =
  match pts with
  | [] -> ()
  | x::pts' ->
    print_pt ~env:env x;
    print_pt_list (EConstr.push_rel x env) pts'


let ps s = Feedback.msg_info (Pp.str s)
