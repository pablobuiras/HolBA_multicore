open HolKernel Parse;
open bir_promisingTheory;
open finite_mapTheory;

val _ = new_theory "bir_promising_diamond";

Definition bir_promising_sim_rel_def:
  sim_rel (cores:num |-> core_t,M:mem_msg_t list) (cores',M') =
   (cores = cores' /\ M = M')
End

Definition bir_promise_step_def:
  promise_step cid (cores,M) (cores',M') =
     (parstep cid cores M cores' M' /\ ~(M = M'))
End

Definition bir_nonpromise_step_def:
  nonpromise_step cid (cores,M) (cores',M') =
  (parstep cid cores M cores' M' /\ (M = M'))
End

Triviality sim_rel_eq:
  sim_rel (cores,M) (cores',M') = (cores = cores' /\ M = M')
Proof
  fs[bir_promising_sim_rel_def]
QED

Theorem promise_inversion:
  parstep cid cores M cores' M' /\ ~(M = M')
==>
  ∃p s s' prom msg.
  cores' = FUPDATE cores (cid, Core cid p s') ∧ FLOOKUP cores cid = SOME (Core cid p s) ∧
  is_certified p cid s' M' ∧
  msg.cid = cid ∧ prom = LENGTH M + 1 ∧ s' = s with bst_prom updated_by (\pr. pr ++ [prom]) ∧
  M' = M ++ [msg]
Proof
  cheat
QED

Theorem execute_inversion:
!cid cores M cores' M'.
  parstep cid cores M cores' M' /\ (M = M')
==>
∃p s s'.
   FLOOKUP cores cid = SOME (Core cid p s)
/\ cores' = FUPDATE cores (cid,Core cid p s)
/\ is_certified p cid s' M'
/\ cstep p cid s M [] s' M'
Proof
   cheat
QED

Theorem promise_cstep:
!p cid s M msg.
    msg.cid = cid
==>
cstep p cid s M [LENGTH M + 1] (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1])) (M ++ [msg])
Proof
  fs[cstep_rules]
QED

Theorem parstep_core_step:
!cid cores M cores' M M' s1 s2 p.
parstep cid cores M cores' M'
/\ FLOOKUP cores cid = SOME (Core cid p s1)
==>
?s2 prom. FLOOKUP cores' cid = SOME (Core cid p s2)
   /\ cstep p cid s1 M prom s2 M'
Proof
  rw[parstep_cases]
  >> Q.EXISTS_TAC ‘s'’ >> Q.EXISTS_TAC ‘prom’
  >> fs[parstep_cases,FLOOKUP_UPDATE]
QED

Theorem certification_extension:
  is_certified p cid s' M
  /\ is_certified p' cid'
     (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]))
      (M ⧺ [msg])
  /\ msg.cid = cid'
==>
  is_certified p cid'
    (s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]))
    (M ⧺ [msg])
Proof
  cheat
QED

Theorem promise_parstep:
!p cid s M2 msg T1.
  FLOOKUP T1 cid = SOME (Core cid p s) /\
     is_certified p cid (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M2 + 1])) (M2 ⧺ [msg]) /\ msg.cid = cid
  ==>
  parstep cid T1 M2
  (FUPDATE T1 (cid, Core cid p
                    (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M2 + 1]))))
  (M2 ⧺ [msg])
Proof
    rpt strip_tac
    >> ‘cstep p cid s M2 [LENGTH M2 + 1] (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M2 + 1])) (M2 ++ [msg])’ by fs[promise_cstep]
    >> cheat
QED

Theorem blah:
!T1 k1 k2 a b.
  ~(k1 = k2)
==>
   FLOOKUP (T1 |+ (k1,a) |+ (k2,b)) k1 =
   FLOOKUP (T1 |+ (k1,a)) k1
Proof
  rpt strip_tac
  >> fs[FLOOKUP_UPDATE]
QED
       

    
Theorem promise_step_non_interference:
 ~(cid = msg.cid) /\ parstep cid T1 M (T1 |+ (cid,core cid p' s')) M
 /\ FLOOKUP (T1 |+ (cid,Core cid p' s')) msg.cid = SOME (core msg.cid p s)
==>
parstep cid (T1 |+ (msg.cid, core msg.cid p (s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1])))) (M1 ++ [msg]) (T1 |+ (cid, Core cid p' s) |+ (msg.cid, core msg.cid p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])))) (M1 ++ [msg])
Proof
  fs[parstep_cases, parstep_rules] >> rpt strip_tac
>> cheat
QED 
    
Theorem bir_promising_diamond:
  !T1 T2 T3 M1 M2 M3 cid cid'.
  (nonpromise_step cid (T1,M1) (T2,M2) /\ promise_step cid' (T2,M2) (T3,M3))
  ==>
  ?T1' T2' T3' M1' M2' M3'.
       sim_rel (T1,M1) (T1',M1')
    /\ promise_step cid' (T1',M1') (T2',M2')
    /\ nonpromise_step cid (T2',M2') (T3',M3')
    /\ sim_rel (T3,M3) (T3',M3')
Proof
  REWRITE_TAC[bir_nonpromise_step_def, bir_promise_step_def]
>> REPEAT STRIP_TAC
>> fs[sim_rel_eq]
>> dxrule promise_inversion
>> rw[]
>> dxrule execute_inversion
>> rw[]
>> Q.EXISTS_TAC ‘FUPDATE T1 (msg.cid, core msg.cid p (s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1])))’
>> Cases_on ‘cid = msg.cid’
(*>| [
    ‘p = p'’ by cheat
    >> ‘is_certified p msg.cid (s' with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])’ by cheat
    >> ‘cstep p msg.cid s' M1 [LENGTH M1 + 1] (s' with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])’ by rw[cstep_rules]
    >> cheat
    ,
    ‘FLOOKUP (FUPDATE T1 (cid,core cid p' s')) msg.cid = FLOOKUP T1 msg.cid’ by cheat
    >> first_x_assum (assume_tac o GSYM)
    >> ‘cstep p msg.cid s' M1 [LENGTH M1 + 1] (s' with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])’ by rw[cstep_rules]
    >> rw[parstep_rules]
    >> cheat
  ]
*)
>> cheat
QED

val _ = export_theory ()
