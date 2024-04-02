Require Import CakeSem.Namespace.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.

Require Import Lists.List.
Import ListNotations.

Definition write_v name v env : sem_env val :=
update_sev env (nsBind name v (sev env)).
Opaque write_v.

Definition write_c name c env : sem_env val :=
update_sec env (nsBind name c (sec env)).
Opaque write_c.

Definition merge_envs env1 env2 : sem_env val :=
  {| sev := nsAppend (sev env1) (sev env2);
     sec := nsAppend (sec env1) (sec env2) |}.
Opaque merge_envs.

Definition write_rec funs cl_env env :=
  fold_right (fun f e =>  write_v (fst (fst f)) (Recclosure cl_env funs (fst (fst f))) e) env funs.

Fixpoint write_c_list cs env :=
  match cs with
  | [] => env
  | (name,stmp)::cs' => write_c name stmp (write_c_list cs' env)
  end.
