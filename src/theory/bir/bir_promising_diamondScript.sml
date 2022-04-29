open HolKernel Parse;
open bir_promisingTheory;
open bir_programTheory;
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

Triviality mem_read_some:
  !M l t v.
    mem_read M l t = SOME v ==> t <= LENGTH M \/ (t = 0 /\ v = mem_default_value)
Proof
  Induct_on ‘t’
  >> rpt strip_tac
  >> fs[mem_read_def]
  >> Cases_on ‘oEL t M’
  >> fs[mem_read_aux_def,listTheory.oEL_EQ_EL, listTheory.oEL_def]
QED


Triviality mem_read_append2:
  !t M l M'.
    t <= LENGTH M ==> mem_read (M++M') l t = mem_read M l t
Proof
  rewrite_tac [GSYM listTheory.SNOC_APPEND]
  >> Induct_on ‘t’ 
  >> fs[mem_read_def]
  >> rpt strip_tac
  >> ‘t <= LENGTH M’ by decide_tac
  >> LAST_ASSUM drule >> rw[mem_read_def, mem_read_aux_def]
  >> fs[listTheory.oEL_THM, listTheory.EL_SNOC, listTheory.EL_APPEND_EQN]
QED

  
Triviality mem_read_append:
!t M l msg.
     t <= LENGTH M ==> mem_read (M++[msg]) l t = mem_read M l t
Proof
  rewrite_tac [GSYM listTheory.SNOC_APPEND]
  >> Induct_on ‘t’ 
  >> fs[mem_read_def]
  >> rpt strip_tac
  >> ‘t <= LENGTH M’ by decide_tac
  >> LAST_ASSUM drule >> rw[mem_read_def, mem_read_aux_def]
  >> fs[listTheory.oEL_THM, listTheory.EL_SNOC]
QED

Triviality sim_rel_eq:
  sim_rel (cores,M) (cores',M') = (cores = cores' /\ M = M')
Proof
  fs[bir_promising_sim_rel_def]
QED

Theorem promise_inversion:
!cid cores M cores' M'.
  parstep cid cores M cores' M' /\ ~(M = M')
==>
  ∃p s s' prom msg.
  cores' = FUPDATE cores (cid, Core cid p s') ∧ FLOOKUP cores cid = SOME (Core cid p s) ∧
  is_certified p cid s' M' ∧
  msg.cid = cid ∧ prom = LENGTH M + 1 ∧ s' = s with bst_prom updated_by (\pr. pr ++ [prom]) ∧
  M' = M ++ [msg]
  ∧ atomicity_ok cid cores
Proof
  rpt strip_tac
>> fs[parstep_cases]
>> fs[cstep_cases]
>> Q.PAT_ASSUM ‘s' = _’ (fn th => fs[th])
>> Q.PAT_ASSUM ‘M' = _’ (fn th => fs[th])
QED

Theorem execute_inversion:
!cid cores M cores'.
  parstep cid cores M cores' M
==>
∃p s s' prom.
   FLOOKUP cores cid = SOME (Core cid p s)
/\ cores' = FUPDATE cores (cid,Core cid p s')
/\ is_certified p cid s' M
/\ cstep p cid s M prom s' M
/\ atomicity_ok cid cores
Proof
  rpt strip_tac
  >> fs[parstep_cases]
  >> Q.EXISTS_TAC ‘s'’
  >> Q.EXISTS_TAC ‘prom’
  >> fs[]
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

Theorem clstep_promise_singleton:
!p cid s M s' h t.
  clstep p cid s M (h::t) s'
==>
   t = []
Proof
  rpt strip_tac
  >> fs[clstep_cases]
QED

Theorem bir_exec_stmt_assign_promise_commutes:
!v ex s f.
bir_exec_stmt_assign v ex (s with bst_prom updated_by f) =
bir_exec_stmt_assign v ex s with bst_prom updated_by f
Proof
  fs[bir_exec_stmt_assign_def, bir_state_set_typeerror_def]
  >> rpt strip_tac
  >> Cases_on ‘bir_eval_exp ex s.bst_environ’ >- fs[]
  >> Cases_on ‘bir_env_write v x s.bst_environ’ >> fs[]
QED

Theorem bir_exec_stmt_assert_promise_commutes:
!ex s f.
bir_exec_stmt_assert ex (s with bst_prom updated_by f) =
bir_exec_stmt_assert ex s with bst_prom updated_by f
Proof
  fs[bir_exec_stmt_assert_def, bir_state_set_typeerror_def]
  >> rpt strip_tac
  >> Cases_on ‘bir_eval_exp ex s.bst_environ’ >- fs[]
  >> Cases_on ‘bir_dest_bool_val x’ >- fs[]
  >> Cases_on ‘x'’ >> fs[]
QED

Theorem bir_exec_stmt_assume_promise_commutes:
!ex s f.
bir_exec_stmt_assume ex (s with bst_prom updated_by f) =
bir_exec_stmt_assume ex s with bst_prom updated_by f
Proof
  fs[bir_exec_stmt_assume_def, bir_state_set_typeerror_def]
  >> rpt strip_tac
  >> Cases_on ‘bir_eval_exp ex s.bst_environ’ >- fs[]
  >> Cases_on ‘bir_dest_bool_val x’ >- fs[]
  >> Cases_on ‘x'’ >> fs[]
QED

Theorem bir_exec_stmt_fence_promise_commutes:
!mop mos s oo s' f.
  bir_exec_stmt_fence mop mos s = (oo,s')
  ==>
  bir_exec_stmt_fence mop mos (s with bst_prom updated_by f)
   = (oo, s' with bst_prom updated_by f)
Proof
  fs[bir_exec_stmt_fence_def]
QED

Theorem bir_exec_stmt_observe_promise_commutes:
  !oid ec el obf s oo s' f.
    bir_exec_stmt_observe oid ec el obf s = (oo,s')
    ==>
    bir_exec_stmt_observe oid ec el obf (s with bst_prom updated_by f)
    = (oo, s' with bst_prom updated_by f)
Proof
  fs[bir_exec_stmt_observe_def, bir_state_set_typeerror_def]
  >> rpt strip_tac
  >> Cases_on ‘bir_eval_exp ec s.bst_environ’ >- (fs[] >> qpat_assum ‘_ = s'’ (SUBST1_TAC o GSYM) >> fs[])
  >> Cases_on ‘bir_dest_bool_val x’ >- (fs[] >> qpat_assum ‘_ = s'’ (SUBST1_TAC o GSYM) >> fs[])
  >> Cases_on ‘x'’
  >> (fs[]
      >> COND_CASES_TAC
      >- (fs[] >> qpat_assum ‘_ = s'’ (SUBST1_TAC o GSYM) >> fs[])
      >> FIRST_ASSUM (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th]))
      >> fs[])
QED

Theorem bir_exec_stmtB_promise_commutes:
!b s oo s' f.
  bir_exec_stmtB b s = (oo,s')
  ==> bir_exec_stmtB b (s with bst_prom updated_by f) = (oo,s' with bst_prom updated_by f)
Proof
  Cases_on ‘b’
  >> fs[bir_exec_stmtB_def,
        bir_exec_stmt_assign_promise_commutes,
        bir_exec_stmt_assert_promise_commutes,
        bir_exec_stmt_assume_promise_commutes,
        bir_exec_stmt_observe_promise_commutes,
        bir_exec_stmt_fence_promise_commutes]
QED

Theorem bir_exec_stmt_jmp_promise_commutes:
!p b s f.
  bir_exec_stmt_jmp p b (s with bst_prom updated_by f) =
  bir_exec_stmt_jmp p b s with bst_prom updated_by f
Proof
    fs[bir_exec_stmt_jmp_def, bir_state_set_typeerror_def]
    >> rpt strip_tac
    >> Cases_on ‘bir_eval_label_exp b s.bst_environ’ >- fs[]
    >> fs[bir_exec_stmt_jmp_to_label_def]
    >> Cases_on ‘MEM x (bir_labels_of_program p)’
    >> fs[]
QED
  
Theorem bir_exec_stmtE_promise_commutes:
!p b s f.
 bir_exec_stmtE p b (s with bst_prom updated_by f) = bir_exec_stmtE p b s with bst_prom updated_by f
Proof
  Cases_on ‘b’
  >> fs[bir_exec_stmtE_def]
  >|
  [fs[bir_exec_stmt_jmp_promise_commutes]
   ,
   fs[bir_exec_stmt_cjmp_def, bir_state_set_typeerror_def]
   >> Cases_on ‘bir_eval_exp b' s.bst_environ’ >- fs[]
   >> rpt strip_tac
   >> Cases_on ‘bir_dest_bool_val x’ >- fs[]
   >> Cases_on ‘x'’ >> fs[bir_exec_stmt_jmp_promise_commutes]
   ,
   fs[bir_exec_stmt_halt_def, bir_state_set_typeerror_def]
   >> Cases_on ‘bir_eval_exp b' s.bst_environ’
   >> fs[]
  ]
QED

Theorem bir_exec_stmt_promise_commutes:
!p stmt s f oo s'.
(bir_exec_stmt p stmt s) = (oo,s')
==>
bir_exec_stmt p stmt (s with bst_prom updated_by f) = (oo,s' with bst_prom updated_by f)
Proof
  REVERSE (Cases_on ‘stmt’) >- fs[bir_exec_stmt_def, bir_exec_stmtE_promise_commutes]
  >> rpt strip_tac
  >> fs[bir_exec_stmt_def]
  >> tmCases_on “bir_exec_stmtB b s” ["oo1 s1"]
  >> tmCases_on “bir_exec_stmtB b (s with bst_prom updated_by f)” ["oo2 s2"]
  >> fs[bir_state_is_terminated_def]
  >> ‘bir_exec_stmtB b (s with bst_prom updated_by f) = (oo1,s1 with bst_prom updated_by f)’
    by fs[bir_exec_stmtB_promise_commutes]
  >> Cases_on ‘s1.bst_status = BST_Running’
  >> Cases_on ‘s2.bst_status = BST_Running’
  >> gs[] >> LAST_ASSUM (SUBST1_TAC o GSYM) >> fs[]
QED

Triviality FILTER_extend_commutes:
  !P f x.
  f = (\pr. pr ++ [x]) /\ P x
  ==>
  FILTER P o f = f o FILTER P
Proof
  rpt strip_tac
  >> irule EQ_EXT >> strip_tac
  >> fs[listTheory.FILTER_APPEND_DISTRIB]
QED

Theorem promises_do_not_disable_clsteps:
! msg p s s' M1 prom.
clstep p msg.cid s M1 prom s'
==>
clstep p msg.cid
      (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))
      (M1 ⧺ [msg]) prom
      (s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))
Proof
Induct_on ‘clstep’
>> rpt strip_tac
>|[
  (* read *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,0))
  >> Q.LIST_EXISTS_TAC [‘v’, ‘a_e’, ‘xcl’,‘acq’,‘rel’, ‘l’, ‘t’, ‘v_pre’, ‘v_post’, ‘v_addr’, ‘var’, ‘new_env’, ‘opt_cast’]
  >> rpt strip_tac >- fs[] >- fs[]
  >|
  [drule mem_read_some >> strip_tac >> fs[mem_read_append]
  ,fs[]
  , (* quantifier case *)
  fs[]
  >> qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
  >> rpt strip_tac
  >> ‘t' ≤ MAX v_pre (s.bst_coh l)’ by fs[bir_state_t_accfupds]
  >> ‘∃msg. oEL (t'-1) M1 = SOME msg ∧ msg.loc ≠ l’ by fs[]
  >> Q.EXISTS_TAC ‘msg''’
  >> fs[listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
  ,fs[]
  ,fs[]
  ,fs[]
  ]
  , (* xclfail *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,1))
  >> Q.LIST_EXISTS_TAC [‘a_e’, ‘v_e’, ‘acq’, ‘rel’, ‘new_env’, ‘new_viewenv’]
  >> fs[xclfail_update_env_def, xclfail_update_viewenv_def]
  , (* fulfil *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,2))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v’,‘l’,‘v_addr’,‘v_data’,‘new_env’, ‘new_viewenv’]
  >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
  >> rpt strip_tac
  >| [
      Cases_on ‘s.bst_xclb’ >- fs[]
      >> fs[] >> DISCH_TAC >> GEN_TAC >> rpt strip_tac
      >> ‘t' < LENGTH M1 + 1’ by DECIDE_TAC
      >> fs[]
      ,
      gvs[]
      >>
      ‘(λpr. pr ⧺ [LENGTH M1 + 1]) ∘ FILTER (λt'. t' ≠ t)
       = FILTER (λt'. t' ≠ t) ∘ (λpr. pr ⧺ [LENGTH M1 + 1])’
        suffices_by fs[]
      >> irule (GSYM FILTER_extend_commutes)
      >> fs[] >> Q.EXISTS_TAC ‘LENGTH M1 + 1’
      >> fs[]
    ]
  , (* amo *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,3))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v_addr’, ‘v_data’, ‘v_post’, ‘l’, ‘v_r’, ‘v_w’, ‘t_r’, ‘new_environ’]
  >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
  >> rpt strip_tac
  >| [drule mem_read_some >> strip_tac >> fs[mem_read_append]
      ,
      gvs[]
      >>
      ‘(λpr. pr ⧺ [LENGTH M1 + 1]) ∘ FILTER (λt'. t' ≠ t_w)
       = FILTER (λt'. t' ≠ t_w) ∘ (λpr. pr ⧺ [LENGTH M1 + 1])’
        suffices_by fs[]
      >> irule (GSYM FILTER_extend_commutes)
      >> fs[] >> Q.EXISTS_TAC ‘LENGTH M1 + 1’
      >> fs[]
     ]
  , (* fence *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,4))
>> fs[bir_programTheory.bir_state_t_accfupds]

  ,(* branch *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,5))
>> fs[bir_programTheory.bir_state_t_accfupds]
>> rw[bir_exec_stmt_promise_commutes]
>> Q.EXISTS_TAC ‘v’ >> Q.EXISTS_TAC ‘oo’ >> Q.EXISTS_TAC ‘s2 with bst_prom updated_by (\pr.pr ++ [LENGTH M1 + 1])’ >> Q.EXISTS_TAC ‘v_addr’
>> drule bir_exec_stmt_promise_commutes
>> rw[]

  ,(* expr *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,6))
  >> Q.LIST_EXISTS_TAC [‘var’, ‘v’, ‘v_val’, ‘e’, ‘new_env’]
  >> fs[bir_programTheory.bir_state_t_accfupds]

  ,(* generic *)
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,7))
>> Q.EXISTS_TAC ‘stm’ >> Q.EXISTS_TAC ‘oo’
>> rw[bir_exec_stmt_promise_commutes]
]
QED
  
  
Theorem certification_extension:
!p cid M s s'' msg prom.
  is_certified p cid s'' M
  /\ is_certified p cid
     (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]))
      (M ⧺ [msg])
  /\ msg.cid = cid
  /\ cstep p cid s M prom s'' M
==>
  is_certified p cid
    (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]))
    (M ⧺ [msg])
Proof
  rpt strip_tac
  >> fs[is_certified_def]
  >> Q.LIST_EXISTS_TAC [‘s'³'’,‘M''’]
  >> fs[cstep_cases]
  >> Q.PAT_ASSUM ‘msg.cid = cid’
      (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  >> drule promises_do_not_disable_clsteps >> rw[]
  >> ‘cstep_seq p msg.cid (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]), M++[msg]) (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]), M++[msg])’ by metis_tac[cstep_seq_rules]
  >> fs[cstep_seq_rtc_def]
  >> metis_tac[relationTheory.RTC_RULES]
QED
(*
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

Theorem promise_step_non_interference:
! cid T1 M p p' s s' msg M1.
         ~(cid = msg.cid) /\ parstep cid T1 M (T1 |+ (cid,Core cid p' s')) M
 /\ FLOOKUP (T1 |+ (cid,Core cid p' s')) msg.cid = SOME (Core msg.cid p s)
==>
parstep cid (T1 |+ (msg.cid, Core msg.cid p (s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1])))) (M1 ++ [msg]) (T1 |+ (cid, Core cid p' s) |+ (msg.cid, Core msg.cid p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])))) (M1 ++ [msg])
Proof
  fs[parstep_cases, parstep_rules] >> rpt strip_tac
>> cheat
QED 
*)
val promise_subst = subst [“s:bir_state_t” |-> “(s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))”, “s':bir_state_t” |-> “(s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))”];

val case1 = “(s' :bir_state_t) =
             (s :bir_state_t) with
                              <|bst_v_rNew :=
                                MAX s.bst_v_rNew
                                    (if is_read (K2 :bir_memop_t) then (v :num) else (0 :num));
                                bst_v_wNew :=
                                MAX s.bst_v_wNew (if is_write K2 then v else (0 :num));
                                bst_pc updated_by bir_pc_next|>”;


Theorem nonpromising_extra_promise:
!msg T1 p s' s M1.
  parstep msg.cid (T1 |+ (msg.cid,Core msg.cid p s')) M1
              (T1 |+ (msg.cid,Core msg.cid p s)) M1
  /\ is_certified p msg.cid (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])
  ==>
  parstep msg.cid (T1 |+ (msg.cid,Core msg.cid p (s' with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])))) (M1 ++ [msg])
          (T1 |+ (msg.cid,Core msg.cid p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])))) (M1 ++ [msg])
Proof
  rpt strip_tac
  >> fs[parstep_cases, FUPD11_SAME_KEY_AND_BASE]
  >> Q.EXISTS_TAC ‘(s' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))’
  >> Q.EXISTS_TAC ‘prom’
  >> fs[FLOOKUP_UPDATE]
  >> fs[atomicity_ok_def]
  >> fs[cstep_cases, promises_do_not_disable_clsteps]
QED

Theorem programs_unchanged:
!cid T1 T2 M1 M2.
  parstep cid T1 M1 T2 M2 ==>
     !p s p' s'.
       FLOOKUP T1 cid = SOME (Core cid p s)
       /\ FLOOKUP T2 cid = SOME (Core cid p' s')
       ==> p = p'
Proof
   rpt strip_tac
>> fs[parstep_cases]
>> last_assum (fn th => fs [th,FLOOKUP_UPDATE])
QED

Theorem bir_promising_diamond_same_core:
  !T1 T2 T3 M1 M2 M3 cid.
  (nonpromise_step cid (T1,M1) (T2,M2) /\ promise_step cid (T2,M2) (T3,M3))
  ==>
  ?T1' T2' T3' M1' M2' M3'.
       sim_rel (T1,M1) (T1',M1')
    /\ promise_step cid (T1',M1') (T2',M2')
    /\ nonpromise_step cid (T2',M2') (T3',M3')
    /\ sim_rel (T3,M3) (T3',M3')
Proof
  REWRITE_TAC[bir_nonpromise_step_def, bir_promise_step_def]
>> REPEAT STRIP_TAC
>> fs[sim_rel_eq]
>> drule execute_inversion >> rw[]
>> drule promise_inversion  >> rw[]
>> fs[FLOOKUP_UPDATE] (* introduces p = p' and s = s'' *)
>> Q.EXISTS_TAC ‘FUPDATE T1 (msg.cid, Core msg.cid p (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1])))’
>> Q.PAT_ASSUM ‘p=p'’ (fn th => once_rewrite_tac [th])
>> ‘is_certified p' msg.cid (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])’ by (
  match_mp_tac certification_extension
  >> Q.LIST_EXISTS_TAC [‘s''’, ‘prom’]
  >> fs[]
   )
>> ‘cstep p' msg.cid s M1 [LENGTH M1 + 1] (s with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1])) (M1 ++ [msg])’ by rw[cstep_rules]
>> strip_tac >| [
    match_mp_tac parstep_rules >> Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘[LENGTH M1 + 1]’ >> fs[],
    ‘parstep msg.cid (T1 |+ (msg.cid, Core msg.cid p' s))
     M1
     (T1 |+ (msg.cid, Core msg.cid p' s''))
     M1’ by (
      ‘T1 |+ (msg.cid, Core msg.cid p' s) = T1’ by fs[flookup_thm,FUPDATE_ELIM] >> fs[])
    >> dxrule nonpromising_extra_promise
    >> fs[FUPDATE_EQ]
    ]
QED

Theorem promises_do_not_disable_clsteps_other_core:
!p cid M prom s s' msg.
~(cid = msg.cid)
/\ clstep p cid s M prom s'
==>
clstep p cid s (M++[msg]) prom s'
Proof
  Induct_on ‘clstep’
  >> rpt strip_tac
  >| [ (* read *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,0))
    >> Q.LIST_EXISTS_TAC [‘v’, ‘a_e’, ‘xcl’, ‘acq’, ‘rel’, ‘l’, ‘t’, ‘v_pre’, ‘v_post’, ‘v_addr’,‘var’, ‘new_env’, ‘opt_cast’]
    >> rpt strip_tac >- fs[] >- fs[]
    >|
    [drule mem_read_some >> strip_tac >> fs[mem_read_append]
     ,fs[]
     , (* quantifier case *)
     qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
     >> rpt strip_tac
     >> ‘t' ≤ MAX v_pre (s.bst_coh l)’ by fs[bir_state_t_accfupds]
     >> ‘∃msg. oEL (t'-1) M = SOME msg ∧ msg.loc ≠ l’ by fs[]
     >> Q.EXISTS_TAC ‘msg'’
     >> fs[listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
     ,fs[]
     ,fs[]
     ,fs[]
    ]
    , (* xclfail *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,1))
    >> Q.LIST_EXISTS_TAC [‘a_e’, ‘v_e’, ‘acq’, ‘rel’, ‘new_env’, ‘new_viewenv’]
    >> fs[xclfail_update_env_def, xclfail_update_viewenv_def]
    ,(* fulfil *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,2))
    >> fs[bir_programTheory.bir_state_t_accfupds]
    >> Q.LIST_EXISTS_TAC [‘v’,‘l’,‘v_addr’,‘v_data’,‘new_env’, ‘new_viewenv’]
    >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
    >> rpt strip_tac
    >> Cases_on ‘s.bst_xclb’ >- fs[]
    >> fs[] >> DISCH_TAC >> GEN_TAC >> rpt strip_tac
    >> ‘t' < LENGTH M + 1’ by DECIDE_TAC
    >> fs[]
    ,(* amo *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,3))
    >> fs[bir_programTheory.bir_state_t_accfupds]
    >> Q.LIST_EXISTS_TAC [‘v_addr’, ‘v_data’, ‘v_post’, ‘l’, ‘v_r’, ‘v_w’, ‘t_r’, ‘new_environ’]
    >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
    >> drule mem_read_some
    >> strip_tac
    >> fs[mem_read_append]
    ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,4))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,5))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v’, ‘oo’, ‘s2’, ‘v_addr’]
  >> rw[bir_exec_stmt_promise_commutes]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,6))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v’, ‘v_val’, ‘new_env’]
  >> fs[]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,7))
  >> rpt HINT_EXISTS_TAC >> fs[]
  ]
QED

Triviality mem_read_take:
  !m n l M v.
  m <= n /\ n <= LENGTH M ==> mem_read (TAKE n M) l m = mem_read M l m
Proof
  Induct_on ‘m’
  >> fs[mem_read_def, mem_read_aux_def]
  >> rpt strip_tac
  >> ‘m <= n’ by decide_tac
  >> ‘m <= LENGTH M’ by decide_tac
  >> ‘m <= LENGTH (TAKE n M)’ by fs[]
  >> fs[listTheory.oEL_THM]
  >> fs[mem_read_def, mem_read_aux_def]
  >> fs[listTheory.EL_TAKE]
QED

(*
Theorem gen_promises_do_not_disable_clsteps_other_core:
  !p cid M prom s s' msg idx.
    ~(cid = msg.cid)
    /\ clstep p cid s M prom s'
    /\ 1 <= idx /\ idx <= LENGTH M
    ==>
    clstep p cid s (LINSERT msg idx M) prom s'
Proof
  fs[LINSERT_def]
  >> Induct_on ‘clstep’
  >> rpt strip_tac
  >| [ (* read *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,0))
    >> Cases_on ‘t < idx - 1’
    >| [
      Q.LIST_EXISTS_TAC [‘v’, ‘a_e’, ‘xcl’, ‘acq’, ‘rel’, ‘l’, ‘t’, ‘v_pre’, ‘v_post’, ‘v_addr’,‘var’, ‘new_env’, ‘opt_cast’]
      >> rpt strip_tac >- fs[] >- fs[]
      >|
      [drule mem_read_some >> strip_tac
       >> fs[mem_read_append2]
       >> fs[mem_read_take]
     ,fs[]
     , (* quantifier case *)
     qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
     >> rpt strip_tac
     >> ‘t' ≤ MAX v_pre (s.bst_coh l)’ by fs[bir_state_t_accfupds]
     >> ‘∃msg. oEL t' M = SOME msg ∧ msg.loc ≠ l’ by fs[]
     >> Q.EXISTS_TAC ‘msg'’
     >> fs[listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
     ,fs[]
     ,fs[]
     ,fs[]
    ]
    , (* xclfail *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,1))
    >> Q.LIST_EXISTS_TAC [‘a_e’, ‘v_e’, ‘acq’, ‘rel’, ‘new_env’, ‘new_viewenv’]
    >> fs[xclfail_update_env_def, xclfail_update_viewenv_def]
    ,(* fulfil *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,2))
    >> fs[bir_programTheory.bir_state_t_accfupds]
    >> Q.LIST_EXISTS_TAC [‘v’,‘l’,‘v_addr’,‘v_data’,‘new_env’, ‘new_viewenv’]
    >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
    >> rpt strip_tac
    >> Cases_on ‘s.bst_xclb’ >- fs[]
    >> fs[] >> DISCH_TAC >> GEN_TAC >> rpt strip_tac
    >> ‘t' < LENGTH M + 1’ by DECIDE_TAC
    >> fs[]
  , (* amo *)
  cheat
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,3))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,4))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v’, ‘oo’, ‘s2’, ‘v_addr’]
  >> rw[bir_exec_stmt_promise_commutes]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,5))
  >> fs[bir_programTheory.bir_state_t_accfupds]
  >> Q.LIST_EXISTS_TAC [‘v’, ‘v_val’, ‘new_env’]
  >> fs[]
  ,
  HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,6))
  >> rpt HINT_EXISTS_TAC >> fs[]
  ]
QED
*)
  
Theorem promises_other_core_commute_alt:
  !p msg1 msg2 s M M'.
    cstep p msg1.cid s M [LENGTH M + 1]
          (s with bst_prom updated_by (\pr.pr++[LENGTH M + 1])) (M ++ M')
    ==>
    cstep p msg1.cid s (M++[msg2]) [LENGTH M + 2]
          (s with bst_prom updated_by (\pr.pr++[LENGTH M + 2])) (M ++ [msg2] ++ [msg1])
Proof
  rpt strip_tac
  >> fs[cstep_cases]
QED

Theorem promises_other_core_commute:
!p msg1 msg2 s M.
  cstep p msg1.cid s M [LENGTH M + 1]
        (s with bst_prom updated_by (\pr.pr++[LENGTH M + 1])) (M ++ [msg1])
==>
  cstep p msg1.cid s (M++[msg2]) [LENGTH M + 2]
        (s with bst_prom updated_by (\pr.pr++[LENGTH M + 2])) (M ++ [msg2] ++ [msg1])
Proof
  rpt strip_tac
  >> fs[cstep_cases]
QED

Theorem clstep_fulfil_other_core:
!p msg' msg s M s'.
(~(msg.cid = msg'.cid)
 /\ clstep p msg'.cid
           (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]))
           (M ⧺ [msg']) [LENGTH M + 1] s')
  ==>
  clstep p msg'.cid
         (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 2]))
         (M ⧺ [msg] ⧺ [msg']) [LENGTH M + 2] s'
Proof
  rpt strip_tac
  >> fs[clstep_cases]
  >| [Q.LIST_EXISTS_TAC [‘v’,‘l’,‘v_addr’,‘v_data’,‘new_env’,‘new_viewenv’]
      >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
      >> cheat
  ,
  cheat]
QED

(*Theorem clstep_reorder:
!p cid s M R msg prom s'.
  clstep p cid s (M ++ R ++ [msg]) prom s'
==>
  ?prom2 s2. clstep p cid s (M ++ [msg] ++ R) prom2 s2
Proof
  Induct_on ‘R’
  >- (rpt strip_tac >> fs[]
      >> Q.LIST_EXISTS_TAC [‘prom’, ‘s'’] >> fs[])
  >> rpt strip_tac
  >> ‘M ++ h::R ++ [msg] = (M ++ [h]) ++ R ++ [msg]’ by fs[]
  >> first_assum (fn th => fs[th])
  >> last_assum drule >> rw[]
  >>
QED
*)

Definition LINSERT_def:
  LINSERT x t xs = TAKE (t-1) xs ++ x :: DROP (t-1) xs
End

Theorem gen_promise_does_not_disable_cstep_seq:
!cid msg p s M s' M' t.
   (~(cid = msg.cid)
    /\ cstep_seq p cid (s,M) (s',M'))
 ==>
   cstep_seq p cid (s,LINSERT msg t M) (s',LINSERT msg t M')
Proof
  cheat
  >> rpt strip_tac
  >> gs[cstep_seq_cases]
  >| [Induct_on ‘R1’ using listTheory.SNOC_INDUCT
      >- (strip_tac
          >> drule_all promises_do_not_disable_clsteps_other_core
          >> rw[]
          >> Q.EXISTS_TAC ‘prom’ >> fs[])
      >> rpt strip_tac
     ]
QED

Theorem promise_list_does_not_disable_cstep_seq:
  !cid p s M s' M'.
    (cstep_seq p cid (s,M) (s',M++M')
    )
    ==>
    !M2. (!m. MEM m M2 ==> ~(cid = m.cid))
    ==> cstep_seq p cid (s,M++M2) (s',M++M2++M')
Proof
  rpt strip_tac
  >> Induct_on ‘M2’ using listTheory.SNOC_INDUCT >- fs[]
  >> gs[cstep_seq_cases]
  >> rpt strip_tac
  >| [‘(∀m. MEM m M2 ⇒ cid ≠ m.cid)’
        by (fs[listTheory.MEM_SNOC] >> strip_tac >> strip_tac >> fs[])
      >> first_assum drule >> strip_tac
      >> ‘~(cid =  x.cid)’ by fs[]
      >> drule_all promises_do_not_disable_clsteps_other_core >> rw[]
      >> HINT_EXISTS_TAC >> fs[]
      ,
      ‘(∀m. MEM m M2 ⇒ cid ≠ m.cid)’
        by (fs[listTheory.MEM_SNOC] >> strip_tac >> strip_tac >> fs[])
      >> first_assum drule >> strip_tac
      >> ‘~(cid =  x.cid)’ by fs[]
      >> ‘?msg. M' = [msg] /\ cid = msg.cid’ by cheat
      >> fs[]
      >> gs[cstep_cases]
      >> ‘LENGTH M + (LENGTH M2 + 2) =  LENGTH M + LENGTH M2 + 2’ by decide_tac
      >> first_assum SUBST1_TAC
      >> ‘LENGTH M + LENGTH M2 = LENGTH (M++M2)’ by fs[]
      >> first_assum SUBST1_TAC
      >> irule clstep_fulfil_other_core >> gvs[]
     ]
QED

Theorem cstep_seq_memory_only_grows:
  !p cid x y.
    cstep_seq p cid x y
    ==>
    ?MSUFF. SND y = SND x++MSUFF
Proof
  rpt strip_tac
  >> fs[cstep_seq_cases]
  >> fs[cstep_cases]
QED

Theorem cstep_seq_rtc_memory_only_grows:
  !p cid x y.
    (cstep_seq p cid)꙳ x y
    ==>
    ?MSUFF. SND y = SND x++MSUFF
Proof
  gen_tac >> gen_tac
  >> Induct_on ‘(cstep_seq p cid)꙳’
  >> rpt strip_tac >- (Q.EXISTS_TAC ‘[]’ >> fs[])
  >> fs[cstep_seq_cases, cstep_cases]
QED
  
Theorem cstep_seq_rtc_monotonicity:
  !cid p M2 x y.
    (!m. MEM m M2 ==> ~(cid = m.cid))
    ==> cstep_seq_rtc p cid x y
    ==> cstep_seq_rtc p cid
                  (FST x, SND x ++ M2)
                  (FST y, SND x ++ M2 ++ (DROP (LENGTH (SND x)) (SND y)))
Proof
  cheat
QED

(*  
Theorem promises_do_not_disable_cstep_seq_rtc:
  !cid msg p x y MSUFF.
    (~(cid = msg.cid)
     /\ cstep_seq_rtc p cid x y
     /\ SND y = SND x ++ MSUFF)
    ==>
    cstep_seq_rtc p cid (FST x,SND x++[msg]) (FST y,SND x ++ [msg] ++ MSUFF)
Proof
  gen_tac >> gen_tac >> gen_tac
  >> fs[cstep_seq_rtc_def]
  >> Induct_on ‘(cstep_seq p cid)꙳’ using relationTheory.RTC_STRONG_INDUCT_RIGHT1 
  >> rpt strip_tac >- (fs[])
  >> fs[]
  >> PairCases_on ‘x’
  >> PairCases_on ‘y'’
  >> PairCases_on ‘y’
  >> fs[]
  >> drule cstep_seq_memory_only_grows >> rw[]
  >> drule_all promises_do_not_disable_cstep_seq >> rw[]
QED
  
Theorem certification_extension_other_core:
!p p' cid s s' s'' M prom msg.
~(cid = msg.cid)
/\ is_certified p cid s' M
/\ cstep p cid s M prom s' M
/\ is_certified (p':string bir_program_t) msg.cid s'' (M++[msg])
==>
is_certified p cid s' (M++[msg])
Proof
  cheat >>
  rpt strip_tac
  >> fs[is_certified_def]
  >> Q.EXISTS_TAC ‘s'³'’
  >> drule promises_do_not_disable_cstep_seq
  >> metis_tac[cstep_seq_rtc_def]
  >> Q.LIST_EXISTS_TAC [‘s'³'’,‘M'++[msg]’]

  >> drule promises_do_not_disable_clsteps_other_core >> rw[]
  >> ‘clstep p cid s (M++[msg]) prom s'’ by fs[]
  >> ‘cstep_seq p cid (s with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]), M++[msg]) (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M + 1]), M++[msg])’ by metis_tac[cstep_seq_rules]
  >> fs[cstep_seq_rtc_def]
  >> metis_tac[relationTheory.RTC_RULES]
QED
*)

Theorem certification_extension_other_core:
  !p p' cid s s' s'' M prom msg.
    ~(cid = msg.cid)
    /\ is_certified p cid s' M
    /\ cstep p cid s M prom s' M
    /\ is_certified (p':string bir_program_t) msg.cid s'' (M++[msg])
    ==>
    is_certified p cid s' (M++[msg])
Proof
 cheat
QED

Theorem bir_promising_diamond_diff_core:
  !T1 T2 T3 M1 M2 M3 cid1 cid2.
    (~(cid1 = cid2)
    /\ nonpromise_step cid1 (T1,M1) (T2,M2)
    /\ promise_step cid2 (T2,M2) (T3,M3))
    ==>
    ?T1' T2' T3' M1' M2' M3'.
      sim_rel (T1,M1) (T1',M1')
      /\ promise_step cid2 (T1',M1') (T2',M2')
      /\ nonpromise_step cid1 (T2',M2') (T3',M3')
      /\ sim_rel (T3,M3) (T3',M3')
Proof
  REWRITE_TAC[bir_nonpromise_step_def, bir_promise_step_def]
  >> REPEAT STRIP_TAC
  >> fs[sim_rel_eq]
  >> drule execute_inversion >> rw[]
  >> drule promise_inversion  >> rw[]
  >> fs[FLOOKUP_UPDATE]
  >> Q.EXISTS_TAC ‘FUPDATE T1 (msg.cid, Core msg.cid p' (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1])))’
  >> strip_tac
  >| [
    match_mp_tac parstep_rules
    >> Q.LIST_EXISTS_TAC [‘s''’, ‘[LENGTH M1+1]’]
    >> fs[atomicity_ok_def, cstep_rules]
    >> LAST_ASSUM (fn th => fs[th])
    >> ‘cores_pc_not_atomic (T1 \\ msg.cid)’ by cheat
    ,
    FULL_SIMP_TAC std_ss [Once FUPDATE_COMMUTES]
    >> match_mp_tac parstep_rules
    >> Q.LIST_EXISTS_TAC [‘s’,‘prom’]
    >> fs[FLOOKUP_UPDATE, atomicity_ok_def]
    >> ‘cores_pc_not_atomic
                (T1 |+
                 (msg.cid,
                  Core msg.cid p'
                       (s'' with bst_prom updated_by (λpr. pr ⧺ [LENGTH M1 + 1]))) \\
                 cid1)’ by cheat
    >> rpt strip_tac >- fs[]
    >| [fs[cstep_cases, promises_do_not_disable_clsteps_other_core]
        ,HO_MATCH_MP_TAC certification_extension_other_core
         >> Q.LIST_EXISTS_TAC
             [‘p'’, ‘s’,
              ‘(s'' with bst_prom updated_by (\pr. pr ++ [LENGTH M1 + 1]))’
              ,‘prom’]
      >> fs[]
      ]
]
QED

val _ = export_theory ()
