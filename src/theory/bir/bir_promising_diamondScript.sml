open HolKernel Parse;
open bir_promisingTheory;
open pred_setTheory;
open finite_setTheory;

val _ = new_theory "bir_promising_diamond";

Definition bir_promising_sim_rel_def:
  sim_rel (cores:core_t -> bool,M:mem_msg_t list) (cores',M') =
   (rel_set $= cores cores' /\ M = M')
End

Definition bir_promise_step_def:
  promise_step (cores,M) (cores',M') =
     (parstep cores M cores' M' /\ ~(M = M'))
End

Definition bir_nonpromise_step_def:
  nonpromise_step (cores,M) (cores',M') =
  (parstep cores M cores' M' /\ (M = M'))
End

Triviality sim_rel_eq:
  sim_rel (cores,M) (cores',M') = (cores = cores' /\ M = M')
Proof
  fs[bir_promising_sim_rel_def]
QED

Theorem promise_inversion:
  parstep cores M cores' M' /\ ~(M = M')
==>
  ∃p cid s s' prom msg.
  cores' = cores DIFF {core cid p s} ∪ {core cid p s'} ∧ core cid p s ∈ cores ∧
  is_certified p cid s' M' ∧
  msg.cid = cid ∧ prom = LENGTH M + 1 ∧ s' = s with bst_prom updated_by (\pr. pr ++ [prom]) ∧
  M' = M ++ [msg]
Proof
  fs[bir_parstep_cases, bir_cstep_cases]
QED

Theorem bir_promising_diamond:
  !T1 T2 T3 M1 M2 M3.
  (nonpromise_step (T1,M1) (T2,M2) /\ promise_step (T2,M2) (T3,M3))
  ==>
  ?T1' T2' T3' M1' M2' M3'.
       sim_rel (T1,M1) (T1',M1')
    /\ promise_step (T1',M1') (T2',M2')
    /\ nonpromise_step (T2',M2') (T3',M3')
    /\ sim_rel (T3,M3) (T3',M3')
Proof
  REWRITE_TAC[bir_nonpromise_step_def, bir_promise_step_def]
>> REPEAT STRIP_TAC
>> fs[sim_rel_eq]
>> cheat
QED

val _ = export_theory ()
