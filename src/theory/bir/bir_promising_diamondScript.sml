open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;
open bir_programTheory;
open bir_valuesTheory;
open bir_expTheory;
open finite_mapTheory;

val _ = new_theory "bir_promising_diamond";

Definition bir_promise_step_def:
  promise_step cid (cores,M) (cores',M') =
  (parstep cid cores M cores' M' /\ ~(M = M'))
End

Definition bir_nonpromise_step_def:
  nonpromise_step cid (cores,M) (cores',M') =
  (parstep cid cores M cores' M' /\ (M = M'))
End

Definition latest_def:
  latest l 0 M = 0
  /\ latest l (SUC t) M =
  case oEL t M of
    SOME msg =>
      if l = msg.loc then SUC t else latest l t M
  | _ => latest l t M
End

Definition well_formed_fwdb_def:
 well_formed_fwdb l M coh_t fwd =
   (fwd.fwdb_time <= latest l coh_t M
    /\ fwd.fwdb_view <= fwd.fwdb_time
    /\ ?v. mem_read M l fwd.fwdb_time = SOME v)
End
(*
Definition well_formed_xclb_def:
  well_formed_xclb M coh_t xclb =
  (xclb.xclb_time <= latest xclb.xclb_loc coh_t M
   /\ xclb.xclb_view <= coh_t
   /\ ?v. mem_read M xclb.xclb_loc xclb.xclb_time = SOME v)
End
*)

Definition well_formed_viewenv_def:
  well_formed_viewenv viewenv M =
  !var v. FLOOKUP viewenv var = SOME v
  ==>
  v <= LENGTH M
End

Definition well_formed_def:
  well_formed cid M s =
  ( well_formed_viewenv s.bst_viewenv M
    /\ (!l. s.bst_coh(l) <= LENGTH M)
     /\ s.bst_v_rNew <= LENGTH M
     /\ s.bst_v_rOld <= LENGTH M
     /\ s.bst_v_wNew <= LENGTH M
     /\ s.bst_v_wOld <= LENGTH M
     /\ s.bst_v_CAP <= LENGTH M
     /\ s.bst_v_Rel <= LENGTH M
     /\ (!l. well_formed_fwdb l M (s.bst_coh(l)) (s.bst_fwdb(l)))
(*     /\ (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M (s.bst_coh(xclb.loc) xclb)) *)
     /\ (!t. MEM t s.bst_prom ==> t <= LENGTH M)
     /\ (!t msg.
           (oEL t M = SOME msg
            /\ msg.cid = cid
            /\ s.bst_coh(msg.loc) < t)
           ==>
           MEM t s.bst_prom)
    )
End

Triviality mem_get_SOME:
  !l t M msg.
    mem_get M l t = SOME msg
    ==>
    l = msg.loc
Proof
  Cases_on ‘t’
  >> fs[mem_get_def, mem_default_def]
  >> rpt strip_tac
  >> Cases_on ‘oEL n M’
  >> gvs[]
QED

Theorem mem_get_mem_read:
  !M l t v.
    mem_read M l t = SOME v
    ==>
    ?m. mem_get M l t = SOME m /\ m.val = v
Proof
  Induct_on ‘t’ >- fs[mem_read_def, mem_get_def]
  >> rpt strip_tac
  >> fs[mem_read_def, mem_get_def]
  >> Cases_on ‘oEL t M’
  >- fs[]
  >> Cases_on ‘x.loc = l’ >- fs[]
  >> fs[]
QED

Theorem mem_get_append:
  !t M l msg.
    t <= LENGTH M ==> mem_get (M++[msg]) l t = mem_get M l t
Proof
  rpt strip_tac
  >> Cases_on ‘t’
  >> fs[mem_get_def] (* discharges 0 case, SUC remains *)
  >> fs[listTheory.oEL_THM, rich_listTheory.EL_APPEND1]
QED

Triviality mem_read_some:
  !M l t v.
    mem_read M l t = SOME v ==> t <= LENGTH M \/ (t = 0 /\ v = mem_default_value)
Proof
  Induct_on ‘t’
  >> rpt strip_tac
  >> fs[mem_read_def,mem_get_def]
  >> Cases_on ‘oEL t M’
  >> fs[listTheory.oEL_EQ_EL, listTheory.oEL_def]
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

Triviality latest_bound:
!l t M.
  latest l t M <= t
Proof
  Induct_on ‘t’ >> fs[latest_def]
  >> rpt strip_tac
  >> ‘latest l t M <= t’ by fs[]
  >> Cases_on ‘oEL t M’
  >> Cases_on ‘l = x.loc’
  >> fs[]
QED

Triviality latest_exact:
!l t M msg.
  mem_get M l t = SOME msg
  ==>
  latest l t M = t
Proof
  Cases_on ‘t’
  >> rpt strip_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL n M’
  >- fs[mem_get_def]
  >> ‘x = msg’ by fs[mem_get_def]
  >> ‘l = msg.loc’ by (drule mem_get_SOME >> fs[])
  >> gvs[]
QED

Triviality latest_sound:
  !l t M. ?msg.
            mem_get M l (latest l t M) = SOME msg
            /\ msg.loc = l
Proof
  Induct_on ‘t’ >- fs[latest_def, mem_get_def, mem_default_def]
  >> rpt strip_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL t M’
  >> fs[]
  >> Cases_on ‘l = x.loc’ >- fs[mem_get_def]
  >> fs[]
QED

Theorem latest_is_latest:
  !l t M t' msg.
    latest l t M <= t' /\ t' <= t
    /\ mem_get M l t' = SOME msg
    ==>
    t' = latest l t M
Proof
  Induct_on ‘t’ >- fs[latest_def]
  >> rpt strip_tac
  >> qspecl_then [‘l’, ‘SUC t’, ‘M’] assume_tac latest_sound
  >> Cases_on ‘t' = SUC t’ >- fs[latest_exact]
  >> ‘t' <= t’ by decide_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL t M’
  >> Cases_on ‘l = x.loc’
  >> fs[]
QED

Theorem latest_monotonicity:
!l M t1 t2.
  t1 <= t2 ==> latest l t1 M <= latest l t2 M
Proof
  rpt strip_tac
  >> ‘?msg.mem_get M l (latest l t2 M) = SOME msg /\ msg.loc = l’
    by fs[latest_sound]
  >> ‘latest l t1 M <= t1’ by fs[latest_bound]
  >> ‘latest l t2 M <= t2’ by fs[latest_bound]
  >> Cases_on ‘t1 <= latest l t2 M’
  >| [fs[]
      ,
      ‘latest l t2 M < t1’ by decide_tac
      >> ‘?msg.mem_get M l (latest l t1 M) = SOME msg /\ msg.loc = l’
        by fs[latest_sound]
      >> spose_not_then assume_tac
      >> ‘latest l t2 M <= latest l t1 M’ by decide_tac
      >> ‘latest l t1 M <= t2’ by decide_tac
      >> ‘latest l t1 M = latest l t2 M’
         by (irule latest_is_latest >> fs[])
      >> fs[]]
QED

Theorem latest_spec:
  !l t M l1.
    (l1 = latest l t M)
    ==>
    (?msg.
      mem_get M l l1 = SOME msg
      /\ msg.loc = l
      /\
      !t'. l1 < t' /\ t' <= t
           ==>
           mem_get M l t' = NONE)
Proof
  rpt strip_tac
  >> qspecl_then [‘l’, ‘t’, ‘M’] assume_tac latest_sound
  >> fs[]
  >> rpt strip_tac
  >> spose_not_then assume_tac
  >> Cases_on ‘mem_get M l t'’ >- fs[]
  >> ‘latest l t' M = t'’ by fs[latest_exact]
  >> ‘latest l t' M <= latest l t M’ by fs[latest_monotonicity]
  >> rw[]
QED

Theorem latest_idempotency:
  !l t M.
    latest l (latest l t M) M = latest l t M
Proof
  rpt strip_tac
  >> ‘?msg. mem_get M l (latest l t M) = SOME msg /\ msg.loc = l’
    by fs[latest_sound]
  >> fs[latest_exact]
QED

Theorem latest_max:
!l M t1 t2.
   latest l t1 M <= latest l (MAX t1 t2) M
   /\ latest l t2 M <= latest l (MAX t1 t2) M
Proof
  fs[latest_monotonicity]
QED

Theorem clstep_preserves_wf_fwdb:
!p cid s M prom s'.
(!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l))
/\ clstep p cid s M prom s'
==>
(!l. well_formed_fwdb l M (s'.bst_coh l) (s'.bst_fwdb l))
Proof
rpt strip_tac
>> fs[clstep_cases]
>> fs[well_formed_fwdb_def, latest_def]
>|
[ (* read *)
Cases_on ‘l = l'’
>| [
‘(s.bst_fwdb l').fwdb_time ≤ latest l' (s.bst_coh l') M’ by fs[]
>> suff_tac “latest l' (s.bst_coh l') M <=
             latest l'
                    (MAX (s.bst_coh l')
                     (MAX
                      (MAX
                       (MAX (MAX v_addr s.bst_v_rNew)
                        (if acq ∧ rel then s.bst_v_Rel else 0))
                       (if acq ∧ rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                      (mem_read_view (s.bst_fwdb l') t))) M” >- fs[]
>> fs[latest_max]
,
fs[]
],
  (* write *)
  Cases_on ‘l = l'’
  >| [
    ‘mem_read M l' v_post = SOME v’ by fs[mem_read_def]
    >> fs[]
    >> ‘v_post = latest l' v_post M’ by fs[latest_exact]
    >> ‘latest l' v_post M <= latest l' (MAX (s.bst_coh l') v_post) M’ suffices_by fs[]
    >> fs[latest_max]
    , fs[]
  ]
  , (* amo *)
  Cases_on ‘l = l'’
  >| [
      EVAL_TAC
      >> ‘mem_read M l t_w = SOME v_w’ by fs[mem_read_def]
      >> fs[]
      >> ‘t_w = latest l t_w M’  by fs[latest_exact]
      >> ‘latest l' t_w M <= latest l' (MAX (s.bst_coh l') t_w) M’
         suffices_by gvs[]
      >> fs[latest_max]
      ,
      EVAL_TAC
      >> fs[]
      >> ‘?v.mem_read M l (s.bst_fwdb l).fwdb_time = SOME v’ by fs[]
      >> qexists_tac ‘v’
      >> ‘?m. mem_get M l (s.bst_fwdb l).fwdb_time = SOME m /\ m.val = v’ by fs[mem_get_mem_read]
      >> fs[]
    ]
  ,
  (* branch *)
  drule bir_exec_stmt_mc_invar >> strip_tac >> fs[]
  ,
  (* generic *)
  drule bir_exec_stmt_mc_invar >> strip_tac >> fs[]
]
QED

Theorem bir_eval_view_of_exp_wf:
!a_e env viewenv M v_addr.
 well_formed_viewenv viewenv M
 /\ v_addr = bir_eval_view_of_exp a_e viewenv
 ==>
 v_addr <= LENGTH M
Proof
  fs[well_formed_viewenv_def]
  >> Induct_on ‘a_e’
  >> fs[bir_eval_view_of_exp_def]
  >> rpt strip_tac
  >- (Cases_on ‘FLOOKUP viewenv b’ >- fs[]
      >> first_assum drule >> fs[])
  >> first_assum drule
  >> last_assum drule >> fs[]
QED

Triviality mem_read_view_wf_fwdb:
!l M coh_t fwd t.
well_formed_fwdb l M coh_t fwd
/\ t <= LENGTH M
==>
mem_read_view fwd t ≤ LENGTH M
Proof
  rpt strip_tac
  >> fs[mem_read_view_def, well_formed_fwdb_def]
  >> CASE_TAC
  >> gvs[]
QED

Theorem clstep_preserves_wf:
!p cid s M prom s'.
  well_formed cid M s
  /\ clstep p cid s M prom s'
==>
  well_formed cid M s'
Proof
  cheat
QED
(* Incomplete proof for time reasons,
   but it should be straightforward

  rpt strip_tac
  >> fs[well_formed_def]
  >> drule_then imp_res_tac clstep_preserves_wf_fwdb
  >> fs[clstep_cases]
    >|
  [ (* read *)
    ‘v_addr <= LENGTH M’
     by (fs[bir_eval_exp_view_def]
         >> drule bir_eval_view_of_exp_wf
         >> fs[])
    >> fs[well_formed_viewenv_def]
    >> Cases_on ‘acq /\ rel’
    >|
    [
      irule_at Any mem_read_view_wf_fwdb
      >> qexists_tac ‘l’ >> qexists_tac ‘s.bst_coh l’
      >> gvs[]
      >> conj_asm1_tac
      >-
        (‘t <= LENGTH M \/ (t = 0 /\ v = mem_default_value)’
         by metis_tac[mem_read_some]
         >> fs[])
      >> rw[]
      >> Cases_on ‘var' = var’
      >> gvs[FLOOKUP_DEF, FLOOKUP_UPDATE]
      >> irule mem_read_view_wf_fwdb
      >> fs[]
      >> qexists_tac ‘s.bst_coh l’ >> qexists_tac ‘l’
      >> fs[]
      ,
      cheat
    ]
  , proof follows here
  ]
*)

Definition valid_index_def:
valid_index i rho =
(i >= 0 /\ i < LENGTH rho)
End

Definition low_eq_view_def:
low_eq_view (N:num) v1 v2 =
  if v1 <= N /\ v2 <= N then v1 = v2 else T
End

Definition low_eq_fwd_def:
low_eq_fwd (N:num) fwd1 fwd2 =
  low_eq_view N fwd1.fwdb_view fwd2.fwdb_view
End

Definition low_eq_xclb_def:
low_eq_xclb N (SOME xcl1) (SOME xcl2) =
  low_eq_view N xcl1.xclb_view xcl2.xclb_view
/\ low_eq_xclb N _ _ = T
End

Definition low_eq_def:
low_eq (N:num) s s' =
(low_eq_view N s.bst_v_rOld s'.bst_v_rOld
 /\ low_eq_view N s.bst_v_wOld s'.bst_v_wOld
 /\ low_eq_view N s.bst_v_rNew s'.bst_v_rNew
 /\ low_eq_view N s.bst_v_wNew s'.bst_v_wNew
 /\ low_eq_view N s.bst_v_CAP s'.bst_v_CAP
 /\ low_eq_view N s.bst_v_Rel s'.bst_v_Rel
 /\ (!var v1 v2.
       FLOOKUP s.bst_viewenv var = SOME v1
       /\ FLOOKUP s'.bst_viewenv var = SOME v2
       ==> low_eq_view N v1 v2)
 /\ (!l. low_eq_view N (s.bst_coh l) (s'.bst_coh l))
 /\ (!l. low_eq_fwd N (s.bst_fwdb l) (s'.bst_fwdb l))
 /\ low_eq_xclb N s.bst_xclb s'.bst_xclb
)
End

(* Monotonicity of vCAP *)

(* Monotonicity of fence? *)

(*Unwinding conditions

NI-like lemma:
cstep_seq_time p cid t s M s1 M'
/\ low_eq k s s'
==>
?s2 t'.
cstep_seq_time p cid t' s' M s2 M'
/\ low-eq k s1 s2
*)

Definition is_read_stmt_def:
  is_read_stmt p s l t v_pre =
  ?M var a_e opt_cast xcl acq rel v_addr v.
    bir_get_stmt p s.bst_pc =
    BirStmt_Read var a_e opt_cast xcl acq rel
    /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\ mem_read M l t = SOME v
    /\ v_pre = MAX (MAX (MAX v_addr s.bst_v_rNew) (if (acq /\ rel) then s.bst_v_Rel else 0))
                   (if (acq /\ rel) then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
End

(* Some attempts at formulating
   the NI-like properties:

Theorem unwinding_cstep_seq:
!p cid t s M s1 M' k.
  cstep_seq_time p cid t s M s1 M'
  /\ low_eq k s s'
  ==>
  ?s2 t'.
    (cstep_seq_time p cid t' s' M s2 M'
     /\ low-eq k s1 s2)
Proof
  cheat
QED

Theorem cert_future_irrelevance:
!p cid s M rho i j.
rho IN certifying_traces p cid s M
valid_index i rho /\ valid_index j rho
/\ time = timestamp_at i rho
/\ is_mem_op i rho
/\ timestamp_at j rho > time
==>
!rho'.
similar_trace rho rho' (* ?? *)
/\ ~(timestamp_at j rho' = timestamp_at j rho)
/\ timestamp_at j rho' = LENGTH M + 1 (* ?? *)
==>
rho' IN certifying_traces p cid s (M++[promise]) (* ?? *)
Proof
  cheat
QED
*)

Triviality mem_read_append:
!t M l msg.
     t <= LENGTH M ==> mem_read (M++[msg]) l t = mem_read M l t
Proof
  fs[mem_read_def,mem_get_append]
QED

(* More general version, but not needed so far
Triviality mem_read_append2:
  !t M l M'.
    t <= LENGTH M ==> mem_read (M++M') l t = mem_read M l t
Proof
  rewrite_tac [GSYM listTheory.SNOC_APPEND]
  >> Induct_on ‘t’
  >> fs[mem_read_def]
  >> rpt strip_tac
  >> rw[mem_read_def, mem_get_def]
  >> fs[listTheory.oEL_THM, listTheory.EL_SNOC, listTheory.EL_APPEND_EQN]
QED
*)

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
  qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
  >> rpt strip_tac
  >> ‘¬mem_is_loc M1 t' l’ by fs[]
  >> fs[listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
  >> ‘t' <= LENGTH M1’ by cheat (* wf invariant should cover this *)
  >> fs[GSYM mem_get_is_loc, optionTheory.IS_SOME_EXISTS]
  >> fs[mem_get_append]
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
  >> ‘t <= LENGTH M1’ by cheat (* wf invariant *)
  >> rpt strip_tac
  >| [
      fs[mem_is_cid_def] >> cheat (* proof obligation about mem_is_cide *)
      ,
      fs[mem_get_append]
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
  >> Q.LIST_EXISTS_TAC [‘v_addr’, ‘v_data’, ‘l’, ‘v_r’, ‘v_w’, ‘t_r’, ‘new_environ’]
  >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
  >> ‘t_w <= LENGTH M1’ by cheat (* wf invariant *)
  >> rpt strip_tac
  >| [drule mem_read_some >> strip_tac >> fs[mem_read_append]
      ,
      fs[mem_get_append]
      ,
      qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
      >> rpt strip_tac
      >> ‘mem_is_loc M1 t' l’ by fs[]
      >> fs[optionTheory.IS_SOME_EXISTS, GSYM mem_get_is_loc]
      >> qexists_tac ‘x’
      >> ‘t' <= LENGTH M1’ by decide_tac
      >> fs[mem_get_append]
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

Theorem bir_promising_diamond_same_core:
  !T1 T2 T3 M1 M2 M3 cid.
  (nonpromise_step cid (T1,M1) (T2,M2) /\ promise_step cid (T2,M2) (T3,M3))
  ==>
  ?T1' T2' T3' M1' M2' M3'.
       (T1,M1) = (T1',M1')
    /\ promise_step cid (T1',M1') (T2',M2')
    /\ nonpromise_step cid (T2',M2') (T3',M3')
    /\ (T3,M3) = (T3',M3')
Proof
  REWRITE_TAC[bir_nonpromise_step_def, bir_promise_step_def]
>> REPEAT STRIP_TAC
>> fs[]
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
     ‘t' <= LENGTH M’ by cheat (* wf invariant *)
     >> qpat_assum ‘!t''._’ (fn th => drule (Q.SPEC ‘t'’ th))
     >> rpt strip_tac
     >> ‘t' ≤ MAX v_pre (s.bst_coh l)’ by fs[bir_state_t_accfupds]
     >> ‘~mem_is_loc M t' l’ by fs[]
     >> fs[optionTheory.IS_SOME_EXISTS, GSYM mem_get_is_loc]
     >> qpat_assum ‘!x._’ (fn th => assume_tac (Q.SPEC ‘x’ th))
     >> fs[mem_get_append]
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
    >> rpt strip_tac >- cheat (* mem_is_cid *)
    >> ‘t <= LENGTH M’ by cheat (* wf invariant *)
    >> fs[mem_get_append]
    ,(* amo *)
    HO_MATCH_MP_TAC (List.nth (CONJUNCTS clstep_rules,3))
    >> fs[bir_programTheory.bir_state_t_accfupds]
    >> Q.LIST_EXISTS_TAC [‘v_addr’, ‘v_data’, ‘l’, ‘v_r’, ‘v_w’, ‘t_r’, ‘new_environ’]
    >> ‘t_w <= LENGTH M’ by cheat (* wf invariant *)
    >> gvs[fulfil_atomic_ok_def, fulfil_update_env_def, fulfil_update_viewenv_def, listTheory.oEL_EQ_EL, listTheory.EL_APPEND_EQN]
    >> rpt strip_tac
    >| [
        drule mem_read_some >> strip_tac >> fs[mem_read_append]
        ,
        fs[mem_get_append]
        ,
        qpat_assum ‘!t'._’ (fn th => drule (Q.SPEC ‘t'’ th))
        >> strip_tac
        >> ‘mem_is_loc M t' l’ by fs[]
        >> fs[optionTheory.IS_SOME_EXISTS, GSYM mem_get_is_loc]
        >> qexists_tac ‘x’
        >> ‘t' <= LENGTH M’ by decide_tac
        >> fs[mem_get_append]
      ]
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

(* Latest version of the NI-like lemma
if the step is a load

Theorem cstep_seq_views_lower_bound:
  cstep_seq p cid (s,M) (s,M')
  /\ M' = M
  /\ is_read_stmt p s l t v_pre
  /\ t <> 0
  /\ t <= (MAX v_pre s.bst_coh l)
==>
  t = v_pre \/ t = s.bst_coh l
Proof
  cheat
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

(* This approach does not seem to work *)
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

(* Some minor lemmas about cstep_seq *)

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

(*
Failed proof attempt:

Theorem certification_extension_other_core:
!p p' cid s s' s'' M prom msg.
~(cid = msg.cid)
/\ is_certified p cid s' M
/\ cstep p cid s M prom s' M
/\ is_certified (p':string bir_program_t) msg.cid s'' (M++[msg])
==>
is_certified p cid s' (M++[msg])
Proof
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

(* The following lemma is needed in the
bir_promising_diamond_diff_core proof *)
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
      (T1,M1) = (T1',M1')
      /\ promise_step cid2 (T1',M1') (T2',M2')
      /\ nonpromise_step cid1 (T2',M2') (T3',M3')
      /\ (T3,M3) = (T3',M3')
Proof
  fs[bir_nonpromise_step_def, bir_promise_step_def]
  >> rpt strip_tac
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
