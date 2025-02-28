(* This file creates names that the plugin can reference in it's code *)
From CakeSem Require CakeAST SemanticsAux Namespace Evaluate.
Require EnvWrangling.
Require RefineInv.
Require EvaluateDecsWrapper.

Register Lists.List.hd as core.list.hd.
Register Lists.List.firstn as core.list.firstn.
Register Lists.List.rev as core.list.rev.

Register CakeAST.StrLit as cake.strlit.
Register CakeAST.pat as cake.pat.
Register CakeAST.Pany as cake.pany.
Register CakeAST.Pvar as cake.pvar.
Register CakeAST.Plit as cake.plit.
Register CakeAST.Pcon as cake.pcon.
Register CakeAST.Pref as cake.pref.
Register CakeAST.Pas as cake.pas.

Register CakeAST.ast_t as cake.ast_t.
Register CakeAST.Atvar as cake.atvar.
Register CakeAST.Atfun as cake.atfun.
Register CakeAST.Attup as cake.attup.
Register CakeAST.Atapp as cake.atapp.

Register CakeAST.Opapp as cake.opapp.

Register CakeAST.exp as cake.exp.
Register CakeAST.ERaise as cake.eraise.
Register CakeAST.EHandle as cake.ehandle.
Register CakeAST.ELit as cake.elit.
Register CakeAST.ECon as cake.econ.
Register CakeAST.EVar as cake.evar.
Register CakeAST.EFun as cake.efun.
Register CakeAST.EApp as cake.eapp.
Register CakeAST.ELog as cake.elog.
Register CakeAST.EIf as cake.eif.
Register CakeAST.EMat as cake.emat.
Register CakeAST.ELet as cake.elet.
Register CakeAST.ELetrec as cake.eletrec.

Register CakeAST.dec as cake.dec.
Register CakeAST.Dlet as cake.dlet.
Register CakeAST.Dletrec as cake.dletrec.
Register CakeAST.Dtype as cake.dtype.
Register CakeAST.Dtabbrev as cake.dtabbrev.
Register CakeAST.Dexn as cake.dexn.
Register CakeAST.Dmod as cake.dmod.
Register CakeAST.Dlocal as cake.dlocal.

Register SemanticsAux.val as cake.val.
Register SemanticsAux.Litv as cake.litv.
Register SemanticsAux.Conv as cake.conv.
Register SemanticsAux.Closure as cake.closure.
Register SemanticsAux.Recclosure as cake.recclosure.

Register SemanticsAux.stamp as cake.stamp.
Register SemanticsAux.TypeStamp as cake.typestamp.
Register SemanticsAux.ExnStamp as cake.exnstamp.

Register SemanticsAux.sem_env as cake.sem_env.
Register SemanticsAux.Build_sem_env as cake.Build_sem_env.
Register SemanticsAux.sec as cake.sec.
Register SemanticsAux.sev as cake.sev.
Register SemanticsAux.empty_sem_env as cake.empty_sem_env.
Register SemanticsAux.extend_dec_env as cake.extend_dec_env.

Register SemanticsAux.Build_state as cake.build_state.
Register SemanticsAux.state_update_next_type_stamp as cake.state_update_next_type_stamp.

Register Namespace.ident as cake.ident.
Register Namespace.Short as cake.short.
Register Namespace.Long as cake.long.
Register Namespace.nsBind as cake.nsbind.
Register Namespace.nsEmpty as cake.nsEmpty.
Register Namespace.nsLookup as cake.nsLookup.

Register RefineInv.good_cons_env as cake.good_cons_env.
Register RefineInv.FUNC as cake.func.
Register RefineInv.EVAL as cake.eval.
Register RefineInv.DECL as cake.DECL.

Register EnvWrangling.write_v as cake.write_v.
Register EnvWrangling.write_c as cake.write_c.
Register EnvWrangling.merge_envs as cake.merge_envs.
Register EnvWrangling.write_rec as cake.write_rec.
Register EnvWrangling.write_c_list as cake.write_c_list.

Register Evaluate.ident_string_beq as cake.ident_string_beq.

Register EvaluateDecsWrapper.wrapped_eval as cake.wrapped_eval.
