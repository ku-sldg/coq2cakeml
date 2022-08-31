(* This file creates names that the plugin can reference in it's code *)
Require CakeSem.CakeAST.
Require Import ZArith.

Definition stupid_test := CakeAST.ELit (CakeAST.IntLit 12%Z).
Register stupid_test as stupid_test.

(* int *)
Register Z0 as Z.zero.
(* lit *)
Register CakeAST.IntLit as cakeast.intlit.
Register CakeAST.CharLit as cakeast.charlit.
Register CakeAST.StrLit as cakeast.strlit.
Register CakeAST.Word8Lit as cakeast.word8lit.
Register CakeAST.Word64Lit as cakeast.word64lit.

(* pat *)
Register CakeAST.Pany as cakeast.pany.
Register CakeAST.Pvar as cakeast.pvar.
Register CakeAST.Plit as cakeast.plit.
Register CakeAST.Pcon as cakeast.pcan.
Register CakeAST.Pref as cakeast.pref.
Register CakeAST.Pas as cakeast.pas.

(* exp *)
Register CakeAST.ERaise as cakeast.eraise.
Register CakeAST.EHandle as cakeast.ehandle.
Register CakeAST.ELit as cakeast.elit.
Register CakeAST.ECon as cakeast.econ.
Register CakeAST.EVar as cakeast.evar.
Register CakeAST.EFun as cakeast.efun.
Register CakeAST.EApp as cakeast.eapp.
Register CakeAST.ELog as cakeast.elog.
Register CakeAST.EIf as cakeast.eif.
Register CakeAST.EMat as cakeast.emat.
Register CakeAST.ELet as cakeast.elet.
Register CakeAST.ELetrec as cakeast.eletrec.
