Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.Utils.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.
Require Import RefineInv.

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
                          eval_exp fuel' (rev es') st env
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

Fixpoint eval_decs (fuel : nat) (st : state nat) (env : sem_env val) (decs : list dec) : state nat * result (sem_env val) val :=
  (* let fix eval_dec fuel st env d : state nat * result (sem_env val) val := *)
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
            match eval_exp fuel [e] st env with
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

(* Require Import Equations.Prop.Equations. *)
(* Require Import StructTact.StructTactics. *)

(* Theorem pmatch_do_pmatch_equiv : forall envC s p v env res, *)
(*     pmatch envC s p v env = res -> do_pmatch envC s p v env = res. *)
(* Proof. *)
(*   induction p; intros; *)
(*     simp pmatch in H. *)
(*   - destruct v; simp pmatch in H. *)
(*   - destruct v; try (destruct o; assumption). *)
(*     destruct o; destruct o0; try assumption. *)
(*     + simp pmatch in H. *)
(*       simpl. *)
(*       break_match; simpl in *; try assumption. *)
(*       break_match; simpl in *; try assumption. *)
(*       break_match; simpl in *; try assumption. *)
(*       break_match; simpl in *; try assumption. *)
(*       break_match; simpl in *; try assumption. *)
(*       clear Heqb Heqb1 Heqp0 Heqo. *)
(*       generalize dependent res. generalize dependent env. generalize dependent l0. *)
(*       * induction l; intros; destruct l0. *)
(*         assumption. *)
(*         assumption. *)
(*         assumption. *)
(*         Transparent pmatch_list. *)
(*         simpl in H. *)
(*         remember (pmatch envC s a v env). symmetry in Heqm. *)
(*         inversion X. clear H0 H2. *)
(*         specialize (IHl X0). clear X0. *)
(*         specialize (H1 v env m Heqm). rewrite H1. destruct m. *)
(*         assumption. *)
(*         assumption. *)
(*         apply IHl. *)
(*         assumption. *)
(*     + simp pmatch in H. *)
(*       simpl. *)
(*       break_match; simpl in *; try assumption. *)
(*       clear Heqb. *)
(*       generalize dependent res. generalize dependent env. generalize dependent l0. *)
(*       * induction l; intros; destruct l0. *)
(*         assumption. *)
(*         assumption. *)
(*         assumption. *)
(*         simpl in H. *)
(*         remember (pmatch envC s a v env). symmetry in Heqm. *)
(*         inversion X. clear H0 H2. *)
(*         specialize (IHl X0). clear X0. *)
(*         specialize (H1 v env m Heqm). rewrite H1. destruct m. *)
(*         assumption. *)
(*         assumption. *)
(*         apply IHl. *)
(*         assumption. *)
(*   - simpl. destruct v; try assumption. *)
(*     simp pmatch in H. *)
(*     break_match; simpl in *; try assumption. *)
(*     break_match; simpl in *; try assumption. *)
(*     apply IHp. assumption. *)
(* Qed. *)

(* Theorem eval_exps_one_step : forall fuel' st env es, *)
(*     eval_exp (S fuel') es st env = *)
(*       match es with *)
(*       | [] => (st, Rval []) *)
(*       | e1::e2::es' => match eval_exp fuel' [e1] st env with *)
(*                     | (st', Rval vs ) => *)
(*                         match eval_exp fuel' (e2::es') st' env with *)
(*                         | (st'', Rval vs') => (st'', match vs with *)
(*                                              | [] => Rval vs' *)
(*                                              | v::_ => Rval (v::vs') *)
(*                                              end) *)
(*                         | res => res *)
(*                         end *)
(*                     | res => res *)
(*                     end *)
(*       | [ERaise e] => match eval_exp fuel' [e] st env with *)
(*                      | (st', Rval (v::_)) => (st', Rerr (Rraise v)) *)
(*                      | res => res *)
(*                      end *)
(*       | [EHandle e l] => match eval_exp fuel' [e] st env with *)
(*                         | (st', Rerr (Rraise v)) => eval_match_exp fuel' l st' env v bind_exn_v *)
(*                         | res => res *)
(*                         end *)

(*       | [ELit l] => (st, Rval [Litv l]) *)

(*       | [EVar n] => match nsLookup ident_string_beq n (sev env) with *)
(*                    | Some v => (st, Rval [v]) *)
(*                    | None => (st, Rerr (Rabort Rtype_error)) *)
(*                    end *)


(*       | [ECon cn es'] => if do_con_check (sec env) cn (List.length es') then *)
(*                           eval_exp fuel' (rev es') st env *)
(*                         else (st, Rerr (Rabort Rtype_error)) *)
(*       | [EFun x e] => (st, Rval [Closure env x e]) *)
(*       | [EApp op es'] => match eval_exp fuel' (rev es') st env with *)
(*                         | (st', Rval vs) => if op_beq op Opapp then *)
(*                                              match do_opapp (rev vs) with *)
(*                                              | Some (env', e) => eval_exp fuel' [e] st' env' *)
(*                                              | None => (st', Rerr (Rabort Rtype_error)) *)
(*                                              end *)
(*                                            else match do_app _ (refs st', ffi st') op (rev vs) with *)
(*                                                 | Some ((refs, ffi), r) => *)
(*                                                     ({| refs := refs *)
(*                                                      ;  ffi  := ffi *)
(*                                                      ;  clock := clock st' *)
(*                                                      ;  next_type_stamp := next_type_stamp st' *)
(*                                                      ;  next_exn_stamp := next_exn_stamp st' |}, *)
(*                                                       list_result r) *)
(*                                                 | None => (st', Rerr (Rabort Rtype_error)) *)
(*                                                 end *)
(*                         | res => res *)
(*                         end *)
(*       | [ELog And e1 e2] => match eval_exp fuel' [e1] st env with *)
(*                            | (st', Rval (v::_)) => if val_beq v (Boolv true) then *)
(*                                                    eval_exp fuel' [e2] st env *)
(*                                                  else if val_beq v (Boolv false) then *)
(*                                                         (st', Rval [v]) *)
(*                                                       else (st', Rerr (Rabort Rtype_error)) *)
(*                            | res => res *)
(*                            end *)

(*       | [ELog Or e1 e2] => match eval_exp fuel' [e1] st env with *)
(*                            | (st', Rval (v::_)) => if val_beq v (Boolv true) then *)
(*                                                    (st', Rval [v]) *)
(*                                                  else if val_beq v (Boolv false) then *)
(*                                                    eval_exp fuel' [e2] st env *)
(*                                                       else (st', Rerr (Rabort Rtype_error)) *)
(*                            | res => res *)
(*                            end *)
(*       | [EIf c t e] => match eval_exp fuel' [c] st env with *)
(*                       | (st', Rval [v]) => if val_beq v ConvTrue then *)
(*                                             eval_exp fuel' [t] st' env *)
(*                                           else if val_beq v ConvFalse then *)
(*                                                  eval_exp fuel' [e] st' env *)
(*                                                else (st', Rerr (Rabort Rtype_error)) *)
(*                       | (st', Rval _) => (st', Rerr (Rabort Rtype_error)) *)
(*                       | res => res *)
(*                       end *)
(*       | [EMat e pes] => match eval_exp fuel' [e] st env with *)
(*                        | (st', Rval (v::vs)) => *)
(*                            eval_match_exp fuel' pes st' env v bind_exn_v *)
(*                        | res => res *)
(*                        end *)
(*       | [ELet o e1 e2] => match eval_exp fuel' [e1] st env with *)
(*                          | (st', Rval [v]) => *)
(*                              eval_exp fuel' [e2] st' (update_sev env (nsOptBind o v (sev env))) *)
(*                          | (st', Rval _) => (st', Rerr (Rabort Rtype_error)) *)
(*                          | res => res *)
(*                          end *)
(*       | [ELetrec funs e] => if NoDup_dec string_dec (map (fun '(x,y,z) => x) funs) then *)
(*                              eval_exp fuel' [e] st (update_sev env (build_rec_env funs env (sev env))) *)
(*                            else (st, Rerr (Rabort Rtype_error)) *)

(*       | [ETannot e t] => eval_exp fuel' [e] st env *)

(*       | [ELannot e t] => eval_exp fuel' [e] st env *)
(*       end. *)
(*   reflexivity. Qed. *)

(* Theorem eval_exps_S_res : forall fuel st env es st' res, *)
(*     res <> Rerr (Rabort Rtimeout_error) -> *)
(*     eval_exp fuel es st env = (st', res) -> eval_exp (S fuel) es st env = (st', res). *)
(* Proof. *)
(*   intros fuel st env es. revert fuel env st. *)
(*   induction es. *)
(*   (* nil *) *)
(*   destruct fuel; intros; simpl in *; [inv H0; contradiction | assumption]. *)
(*   (* cons *) *)
(*   destruct es. *)
(*   (* nil *) *)
(*   clear IHes. *)
(*   induction a; intros fuel env st st' res Herr H; *)
(*     destruct fuel; try (simpl in H; inv H; contradiction); try assumption. *)
(*   Opaque eval_exp. *)
(*   - rewrite eval_exps_one_step in *. *)
(*     remember (eval_exp fuel [a] st env). symmetry in Heqp. destruct p. *)
(*     destruct r. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*     destruct e. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*     destruct a0. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*     inv H; contradiction. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*   - rewrite eval_exps_one_step in *; try assumption. *)
(*     remember (eval_exp fuel [a] st env). symmetry in Heqp. destruct p. *)
(*     destruct r. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*     destruct e. *)
(*     assert (eval_exp (S fuel) [a] st env = (s, Rerr (Rraise v))) by *)
(*       (apply IHa; try assumption; try discriminate). *)
(*     rewrite H0. *)
(*     (* induction on l *) *)
(*     clear Heqp. clear H0. *)
(*     generalize dependent fuel. *)
(*     induction l. *)
(*     (*1*) intros. clear X. clear IHa. *)
(*       destruct fuel. inv H. contradiction. *)
(*       assumption. *)
(*     (*2*) intros. clear IHa. *)
(*       destruct fuel. inv H. contradiction. *)
(*       inversion X. destruct a0. clear H1 H2. *)
(*       specialize (IHl X1). clear X1. *)
(*       simpl in X0. *)
(*       simpl in H. simpl. *)
(*       break_match. *)
(*       break_match. *)
(*       apply IHl. assumption. *)
(*       assumption. *)
(*       apply X0. *)
(*       assumption. *)
(*       assumption. *)
(*       assumption. *)
(*     destruct a0. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*     inv H. contradiction. *)
(*     apply IHa in Heqp; try discriminate. *)
(*     rewrite Heqp; assumption. *)
(*   - rewrite eval_exps_one_step in *; try assumption. *)
(*     break_match; try assumption. *)
(*     generalize dependent fuel. *)
(*     clear Heqb. *)
(*     apply Forall''_rev in X. *)
(*     revert st st' env Herr. *)
(*     generalize dependent res. *)
(*     induction (rev l); intros; simpl. *)
(*     + destruct fuel. *)
(*       inv H. contradiction. *)
(*       Transparent eval_exp. *)
(*       assumption. *)
(*       Opaque eval_exp. *)
(*     + inversion X. clear H0 H2 X. *)
(*       specialize (IHl0 X0). clear X0. *)
(*       destruct fuel. *)
(*       inv H. contradiction. *)
(*       destruct l0. *)
(*       apply H1; try discriminate; try assumption. *)
(*       rewrite eval_exps_one_step in H. *)
(*       rewrite eval_exps_one_step. *)
(*       break_match; *)
(*         break_match_hyp. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * break_match_hyp. *)
(*         apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * break_match_hyp. *)
(*         apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e0; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a1; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a1; try discriminate. *)
(*         inv H; contradiction. *)
(*       * apply H1 in Heqp. rewrite Heqp. *)
(*         break_match; try assumption. *)
(*         break_match_hyp; try assumption. *)
(*         apply IHl0 in Heqp0. *)
(*         rewrite Heqp0. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*         break_match; try assumption. *)
(*         break_match; try discriminate. *)
(*         destruct e1; try discriminate. *)
(*         destruct a0; try discriminate. *)
(*         inv H; contradiction. *)
(*   - apply Forall''_rev in X. *)
(*     rewrite eval_exps_one_step in H. *)
(*     rewrite eval_exps_one_step. *)
(*     induction (rev l). *)
(*     intros. *)
(*     break_match_hyp. *)
(*     break_match. *)
(*     Transparent eval_exp. *)
(*     destruct fuel. *)
(*     simpl in Heqp, Heqp0. *)
(*     inv Heqp. inv Heqp0. *)
(*     inv H. contradiction. *)
(*     simpl in Heqp, Heqp0. *)
(*     inv Heqp. inv Heqp0. *)
(*     break_match. *)
(*     break_match. *)
(*     Transparent do_opapp. *)
(*     simpl in Heqo0. *)
(*     inv Heqo0. *)
(*     assumption. *)
(*     break_match. *)
(*     simpl in Heqo0. *)
(*     destruct o; try inv Heqo0. *)
(*     destruct w; try inv Heqo0. *)
(*     destruct w; try inv Heqo0. *)
(*     destruct w; try inv Heqo0. *)
(*     destruct w; try inv Heqo0. *)
(*     assumption. *)
(*     inversion X. clear H0 H2. *)
(*     specialize (IHl0 X0). clear X0. clear X. *)
(*     remember (eval_exp fuel (a::l0) st env). symmetry in Heqp. *)
(*     destruct p. *)

(* Theorem eval_exps_forms_equiv : forall st env es st' res fuel, *)
(*     res <> Rerr (Rabort Rtimeout_error) -> *)
(*    eval_or_match true es fuel st env uu uu = (st', res) -> exists fuel', eval_exp fuel' es st env = (st', res). *)
(* Proof. *)
(*   intros st env es st' res fuel HresNoTimeout. *)
(*   funelim (eval_or_match true es fuel st env uu uu). *)
(*   - intro H. exists 1. simpl. rewrite Heqcall. assumption. *)
(*   - intro H. exists 1. simpl. rewrite Heqcall. assumption. *)
(*   - intro H. exists 1. simpl. rewrite Heqcall. assumption. *)
(*   - intro H. rewrite H in Heqcall. inv Heqcall. contradiction. *)
(*   - intro H'. *)
(*     break_match. *)
(*     + rewrite H' in Heqcall. *)
(*       specialize (H n st' res HresNoTimeout Heqcall). *)
(*       destruct H. *)
(*       exists (S x). *)
(*       simpl. *)
(*       break_match. apply H. apply n0 in n. inv n. *)
(*     + exists (S fuel). simpl. *)
(*       break_match. apply n in n0. inv n0. *)
(*       rewrite Heqcall. assumption. *)
(*   - intro H'. *)
(*     rewrite H' in Heqcall. *)
(*     specialize (H st' res HresNoTimeout Heqcall). *)
(*     inv H. *)
(*     exists (S x). simpl. *)
(*     assumption. *)
(*   - intro H'. *)
(*     rewrite H' in Heqcall. *)
(*     specialize (H st' res HresNoTimeout Heqcall). *)
(*     inv H. *)
(*     exists (S x). simpl. *)
(*     assumption. *)
(*   - intro H'. *)
(*     assert (@Rval (list val) val [] <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*     specialize (Hind s (Rval []) H Heq). *)
(*     destruct Hind. *)
(*     exists (S x). simpl. *)
(*     rewrite H0. *)
(*     rewrite Heqcall. *)
(*     assumption. *)
(*   - intro H'. *)
(*     assert (@Rval (list val) val (v::l) <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*     specialize (Hind st' (Rval (v::l)) H Heq). *)
(*     destruct Hind. *)
(*     exists (S x). simpl. *)
(*     rewrite H0. *)
(*     rewrite Heqcall. *)
(*     assumption. *)
(*   - intro H'. *)
(*     destruct e. *)
(*     + assert (@Rerr (list val) val (Rraise v) <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*       specialize (Hind s (Rerr (Rraise v)) H Heq). *)
(*       destruct Hind. *)
(*       exists (S x). simpl. *)
(*       rewrite H0. *)
(*       rewrite Heqcall. *)
(*       assumption. *)
(*     + destruct a. *)
(*       * assert (@Rerr (list val) val (Rabort Rtype_error) <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*         specialize (Hind s (Rerr (Rabort Rtype_error)) H Heq). *)
(*         destruct Hind. *)
(*         exists (S x). simpl. *)
(*         rewrite H0. *)
(*         rewrite Heqcall. *)
(*         assumption. *)
(*       * rewrite H' in Heqcall. inv Heqcall. *)
(*         contradiction. *)
(*       * assert (@Rerr (list val) val (Rabort (Rffi_error f)) <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*         specialize (Hind s (Rerr (Rabort (Rffi_error f))) H Heq). *)
(*         destruct Hind. *)
(*         exists (S x). simpl. *)
(*         rewrite H0. *)
(*         rewrite Heqcall. *)
(*         assumption. *)
(*   - assert (@Rval (list val) val l0 <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*     specialize (Hind s (Rval l0) H Heq). *)
(*     destruct Hind. *)
(*     exists (S x). simpl. *)
(*     rewrite H0. *)
(*     rewrite Heqcall. *)
(*     assumption. *)
(*   - clear H. *)
(*     assert (@Rerr (list val) val (Rraise v) <> Rerr (Rabort Rtimeout_error)) by discriminate. *)
(*     specialize (Hind st' (Rerr (Rraise v)) H Heq). *)
(*     destruct Hind. *)
(*     generalize dependent x. *)
(*     funelim (eval_or_match false l fuel st' env v bind_exn_v). *)
(*     + intros. exists (S x). *)
(*       simpl. rewrite H0. *)
(*       simpl. rewrite H1 in Heqcall. rewrite Heqcall in Heqcall0. *)
(*       destruct x. inv H0. *)
(*       simpl. *)
(*       simp eval_or_match in Heqcall. *)
(*     + clear H0. intros. *)
(*       simp eval_or_match in H2, Heqcall. *)
(*       break_match. *)
(*       specialize (H n e' st0 Heq). clear Heq. *)
(*       specialize (H st res HresNoTimeout). clear HresNoTimeout. *)
(*       rewrite H2. destruct x. inversion H2. *)
(*       clear H0. *)
(*       simpl. *)
(*       break_match. *)
(*       break_match_hyp. *)
(*       apply pmatch_do_pmatch_equiv in Heqm. *)
(*       rewrite Heqm. *)





(* Theorem eval_decs_forms_equiv : forall st env ds st' v, *)
(*    (exists fuel, evaluate_decs fuel st env ds = (st', Rval v)) <-> exists fuel', eval_decs fuel' st env ds = (st', Rval v). *)
(* Proof. *)
(*   intros st env ds. *)
(*   generalize dependent st. *)
(*   generalize dependent env. *)
(*   induction ds; split; intros H. *)
(*   - destruct H. *)
(*     simp evaluate_decs in H. *)
(*     exists 1. *)
(*     simpl. *)
(*     assumption. *)
(*   - destruct H. *)
(*     destruct x. *)
(*     inv H. *)
(*     simpl in H. *)
(*     eexists. *)
(*     simp evaluate_decs. *)
(*   - destruct H. *)
(*     exists (List.length (a::ds) + x). *)
(*     simpl. *)
(*     destruct ds. *)
(*     + destruct a; simp evaluate_decs in H. *)
(*       * break_match. *)
(*         destruct (eval_or_match true [e] x st env uu uu) *)

(* Transparent evaluate_decs. *)
(* Transparent pmatch. *)
(* Transparent eval_or_match. *)
(* Eval compute in (eval_decs_wrapper (init_st _ 0) empty_sem_env [cake_map]). *)
