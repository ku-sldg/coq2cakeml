Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.Utils.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.
Require Import RefineInv.

From Equations Require Import Equations.

Definition dummy_ffi_state (A : Type) (a : A) :=
  let ffi_res := FFI.Oracle_return A a nil in
  let ffi_func := fun _ _ _ => ffi_res in
  let ffi_oracle := fun _ _ => ffi_func in
  FFI.initial_ffi_state (ffi_oracle a) a.

Definition cake_map := Dlet [] (Pvar "map") (EFun "f"
      (ELetrec
         [("map", "l",
           EMat (EVar (Short "l"))
             [(Pcon (Some (Short "Nil")) [], ECon (Some (Short "Nil")) []);
              (Pcon (Some (Short "Cons")) [Pvar "a"; Pvar "t"],
               ECon (Some (Short "Cons"))
                 [EApp Opapp [EVar (Short "f"); EVar (Short "a")];
                  EApp Opapp [EVar (Short "map"); EVar (Short "t")]])])]
         (EVar (Short "map")))).


Definition init_st (A : Type) (a : A) : state A :=
  {| clock := 0
  ; refs  := empty_store
  ; ffi   := dummy_ffi_state A a
  ; next_type_stamp := 0
  ; next_exn_stamp  := 0 |}.


Open Scope list_scope.

Fixpoint do_pmatch (envC : env_ctor) (s : store val) (p : pat) (v : val) (env : alist varN val) : match_result (alist varN val) :=
  let fix do_pmatch_list (envC : env_ctor) (s : store val) (ps : list pat) (vs : list val) (env : alist varN val): match_result (alist varN val) :=
    match ps, vs with
    | [], [] => Match env
    | p::ps',v::vs' => match do_pmatch envC s p v env with
                    | Match env' => do_pmatch_list envC s ps' vs' env'
                    | No_match => No_match
                    | Match_type_error => Match_type_error
                    end
    | _,_ => Match_type_error
    end
  in match p, v with
     | Pany, _ => Match env
     | Pvar x, v => Match ((x,v)::env)
     | Plit l, Litv l' => if lit_beq l l' then
                           Match env
                         else if lit_same_type l l' then
                                No_match
                              else Match_type_error
     | Pcon (Some cid) ps, Conv (Some stamp) vs =>
         match nsLookup ident_string_beq cid envC with
         | None => Match_type_error
         | Some (l, stamp') => if stamp_same_type stamp stamp' && (Nat.eqb (List.length ps) l) then
                                if same_ctor stamp stamp' then
                                  if Nat.eqb (List.length vs) l then
                                    do_pmatch_list envC s ps vs env
                                  else Match_type_error
                                else No_match
                              else Match_type_error
         end
     | Pcon None ps, Conv None vs => if Nat.eqb (List.length ps) (List.length vs) then
                                      do_pmatch_list envC s ps vs env
                                    else Match_type_error
     | Pref p', Loc lnum => match store_lookup lnum s with
                           | None => Match_type_error
                           | Some (Refv v') => do_pmatch envC s p' v' env
                           | Some (W8array _) => Match_type_error
                           | Some (Varray _) => Match_type_error
                           end
     | Pas p' i, v' => do_pmatch envC s p' v' ((i,v)::env)

     | Ptannot p' _, v' => do_pmatch envC s p' v' env

     | _,_ => Match_type_error
     end.

Fixpoint eval_exp (fuel : nat) (es : list exp) (st : state nat) (env : sem_env val) : state nat * result (list val) val :=
  match fuel with
  | O => (st, Rerr (Rabort Rtimeout_error))
  | S fuel' =>
      match es with
      | [] => (st, Rval [])
      | e1::e2::es' => match eval_exp fuel' [e1] st env with
                    | (st', Rval vs ) =>
                        match eval_exp fuel' (e2::es') st' env with
                        | (st'', Rval vs') => (st'', match vs with
                                             | [] => Rval vs'
                                             | v::_ => Rval (v::vs')
                                             end)
                        | res => res
                        end
                    | res => res
                    end
      | [ERaise e] => match eval_exp fuel' [e] st env with
                     | (st', Rval (v::_)) => (st', Rerr (Rraise v))
                     | res => res
                     end
      | [EHandle e l] => match eval_exp fuel' [e] st env with
                        | (st', Rerr (Rraise v)) => eval_match_exp fuel' l st' env v bind_exn_v
                        | res => res
                        end

      | [ELit l] => (st, Rval [Litv l])

      | [EVar n] => match nsLookup ident_string_beq n (sev env) with
                   | Some v => (st, Rval [v])
                   | None => (st, Rerr (Rabort Rtype_error))
                   end


      | [ECon cn es'] => if do_con_check (sec env) cn (List.length es') then
                          match eval_exp fuel' (rev es') st env with
                          | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                             | Some v' => (st', Rval [v'])
                                             | None => (st', Rerr (Rabort Rtype_error))
                                             end
                          | res => res
                          end
                        else (st, Rerr (Rabort Rtype_error))

      | [EFun x e] => (st, Rval [Closure env x e])
      | [EApp op es'] => match eval_exp fuel' (rev es') st env with
                        | (st', Rval vs) => if op_beq op Opapp then
                                             match do_opapp (rev vs) with
                                             | Some (env', e) => eval_exp fuel' [e] st' env'
                                             | None => (st', Rerr (Rabort Rtype_error))
                                             end
                                           else match do_app _ (refs st', ffi st') op (rev vs) with
                                                | Some ((refs, ffi), r) =>
                                                    ({| refs := refs
                                                     ;  ffi  := ffi
                                                     ;  clock := clock st'
                                                     ;  next_type_stamp := next_type_stamp st'
                                                     ;  next_exn_stamp := next_exn_stamp st' |},
                                                      list_result r)
                                                | None => (st', Rerr (Rabort Rtype_error))
                                                end
                        | res => res
                        end
      | [ELog And e1 e2] => match eval_exp fuel' [e1] st env with
                           | (st', Rval (v::_)) => if val_beq v (Boolv true) then
                                                   eval_exp fuel' [e2] st env
                                                 else if val_beq v (Boolv false) then
                                                        (st', Rval [v])
                                                      else (st', Rerr (Rabort Rtype_error))
                           | res => res
                           end

      | [ELog Or e1 e2] => match eval_exp fuel' [e1] st env with
                           | (st', Rval (v::_)) => if val_beq v (Boolv true) then
                                                   (st', Rval [v])
                                                 else if val_beq v (Boolv false) then
                                                   eval_exp fuel' [e2] st env
                                                      else (st', Rerr (Rabort Rtype_error))
                           | res => res
                           end
      | [EIf c t e] => match eval_exp fuel' [c] st env with
                      | (st', Rval [v]) => if val_beq v ConvTrue then
                                            eval_exp fuel' [t] st' env
                                          else if val_beq v ConvFalse then
                                                 eval_exp fuel' [e] st' env
                                               else (st', Rerr (Rabort Rtype_error))
                      | (st', Rval _) => (st', Rerr (Rabort Rtype_error))
                      | res => res
                      end
      | [EMat e pes] => match eval_exp fuel' [e] st env with
                       | (st', Rval (v::vs)) =>
                           eval_match_exp fuel' pes st' env v bind_exn_v
                       | res => res
                       end
      | [ELet o e1 e2] => match eval_exp fuel' [e1] st env with
                         | (st', Rval [v]) =>
                             eval_exp fuel' [e2] st' (update_sev env (nsOptBind o v (sev env)))
                         | (st', Rval _) => (st', Rerr (Rabort Rtype_error))
                         | res => res
                         end
      | [ELetrec funs e] => if nodup_str (map (fun '(x,y,z) => x) funs) then
                             eval_exp fuel' [e] st (update_sev env (build_rec_env funs env (sev env)))
                           else (st, Rerr (Rabort Rtype_error))

      | [ETannot e t] => eval_exp fuel' [e] st env

      | [ELannot e t] => eval_exp fuel' [e] st env
      end
  end
with eval_match_exp (fuel : nat) (pes : list (pat * exp)) (st : state nat) (env : sem_env val) (matched_v err_v : val) : state nat * result (list val) val :=
       match fuel with
       | O => (st, Rerr (Rabort Rtimeout_error))
       | S fuel' => match pes with
                   | [] => (st, Rerr (Rraise err_v))
                   | (p,e)::pes' => if nodup_str (pat_bindings p []) then
                                    match do_pmatch (sec env) (refs st) p matched_v [] with
                                    | Match env_v' =>
                                        eval_exp fuel' [e] st
                                                 {| sev := nsAppend (alist_to_ns env_v') (sev env)
                                                 ;  sec := (sec env) |}
                                    | No_match =>  eval_match_exp fuel' pes' st env matched_v err_v
                                    | Match_type_error => (st, Rerr (Rabort Rtype_error))
                                    end
                                  else (st, Rerr (Rabort Rtype_error))
                   end

       end.

Definition wrapped_eval e env :=
  match eval_exp 1000 [e] (init_st nat 0) env with
  | (_, Rval []) => Litv (StrLit "impossible") (* Not possible *)
  | (_, Rval (v::_)) => v
  | (_, Rerr (Rraise err)) => err
  | (_, Rerr (Rabort _)) => Litv (StrLit "program failure")
  end.

Theorem singular_rec_fun_equiv_DLet_DLetrec : forall f st env locs funname var e,
    evaluate_decs f st env [Dlet locs (Pvar funname) (ELetrec [(funname,var,e)] (EVar (Short funname)))] =
      evaluate_decs f st env [Dletrec locs [(funname,var,e)]].
Proof.
  intros.
  simp evaluate_decs; simpl.
  simp eval_or_match; simpl.
  unfold build_rec_env; simpl.
  unfold nsBind; simpl.
  unfold nsLookup. simpl.
  rewrite eqb_refl. simpl.
  simp pmatch. simpl.
  reflexivity.
Qed.

Fixpoint eval_decs (fuel : nat) (st : state nat) (env : sem_env val) (decs : list dec) : state nat * result (sem_env val) val :=
  match fuel with
  | O => (st, Rerr (Rabort Rtimeout_error))
  | S fuel' =>
      let fuel := fuel' in
      match decs with
      | [] => (st, Rval empty_sem_env)
      | d1::d2::ds =>
          match eval_decs fuel st env [d1] with
          | (st1, Rval env1) =>
              let '(st2,r) := eval_decs fuel st1 (extend_dec_env env1 env) (d2::ds) in
              (st2, combine_dec_result env1 r)
          | res => res
          end
      | [Dlet locs p e] =>
          if nodup_str (pat_bindings p []) then
            let (st',res) := eval_exp fuel [e] st env in
            let res' := match res with
                        | Rval [Recclosure env' [(n,v,e')] n'] =>
                            (st', Rval [Recclosure env' [(n,v,e')] n'])
                        | _ => (st', res)
                        end
            in
            match res' with
            | (st', Rval v) =>
                (st', match do_pmatch (sec env) (refs st') p (hd (Conv None []) v) [] with
                      | Match new_vals => Rval {| sec := nsEmpty; sev := alist_to_ns new_vals |}
                      | No_match => Rerr (Rraise bind_exn_v)
                      | Match_type_error => Rerr (Rabort Rtype_error)
                      end)
            | (st', Rerr err) => (st', Rerr err)
            end
          else (st, Rerr (Rabort Rtype_error))

      | [Dletrec locs funs] =>
          (st, if nodup_str (map (fun x => fst (fst x)) funs) then
                 Rval {| sev := build_rec_env funs env nsEmpty; sec := nsEmpty |}
               else Rerr (Rabort Rtype_error))

      | [Dtype locs tds] =>
          if unique_ctros_in_defs tds then
            (state_update_next_type_stamp st (next_type_stamp st + List.length tds),
              Rval {| sev := nsEmpty; sec := build_tdefs (next_type_stamp st) tds |})
          else (st, Rerr (Rabort Rtype_error))

      | [Dtabbrev _ _ _ _] => (st, Rval {| sev := nsEmpty; sec := nsEmpty |})

      | [Dexn locs cn ts] =>
          (state_update_next_exn_stamp st ((next_exn_stamp st) + 1),
            Rval {| sev := nsEmpty; sec := nsSing cn (List.length ts, ExnStamp (next_exn_stamp st)) |})

      | [Dmod mn ds] =>
          match eval_decs fuel st env ds with
          | (st', Rval env') => (st', Rval {| sev := nsLift mn (sev env'); sec := nsLift mn (sec env') |})
          | res => res
          end

      | [Dlocal ds1 ds2] =>
          match eval_decs fuel st env ds1 with
          | (st1, Rval env1) =>
              eval_decs fuel st1 (extend_dec_env env1 env) ds2
          | res => res
          end
      end
  end.

Definition eval_decs_wrapper st env decs :=
  let '(st',res) := eval_decs 1000 st env decs in
  match res with
  | Rval env' => (st', env')
  | _ => (init_st nat 0, empty_sem_env)
  end.

Definition EVAL_wrapper (st_env : state nat * sem_env val) e inv :=
  let '(st,env) := st_env in
  EVAL env e inv.

Definition DECL_wrapper (st_env : state nat * sem_env val) decs st' env' :=
  let '(st,env) := st_env in
  DECL st env decs st' env'.
