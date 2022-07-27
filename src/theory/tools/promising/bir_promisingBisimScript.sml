open HolKernel Parse boolLib bossLib;
open BasicProvers;
open relationTheory;
open bir_programTheory bir_promisingTheory;
open listTheory rich_listTheory;
open finite_mapTheory;
open dep_rewrite;
open arithmeticTheory;

val _ = new_theory "bir_promisingBisim";

(* difference between indexing into M with and without NONE values
   corresponds to 1 plus the index from EL_FILTER
   "+1" as all indices into the memory list will be substracted by one *)
Definition offset_none_def:
  offset_none M t = t + (LENGTH $ FILTER IS_SOME $ TAKE (PRE t) M) - (LENGTH $ TAKE (PRE t) M)
End

(* TODO move *)
(* general properties *********************************************************)

Theorem cstep_mem_IS_PREFIX:
  !p cid s M genv prom s' M' genv'.
    cstep p cid s M genv prom s' M' genv' ==> M <<= M'
Proof
  ho_match_mp_tac cstep_ind
  >> fs[IS_PREFIX_APPEND]
QED

Theorem I_EQ_IDABS:
  I = λx. x
Proof
  fs[FUN_EQ_THM]
QED

(* move from  ls  to  FILTER P ls  *)
Theorem EL_FILTER:
  !ls n P. n < LENGTH ls /\ P $ EL n ls
  ==> EL (n + (LENGTH $ FILTER P $ TAKE n ls) - (LENGTH $ TAKE n ls)) $ FILTER P ls = EL n ls
  /\ (n + (LENGTH $ FILTER P $ TAKE n ls) - (LENGTH $ TAKE n ls)) < LENGTH $ FILTER P ls
Proof
  Induct >> rw[] >> Cases_on `n` >> fs[]
  >> drule_then assume_tac EL_MEM
  >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
  >> pop_assum $ ONCE_REWRITE_TAC o single
  >> fs[FILTER_APPEND_DISTRIB]
QED

(* move from  FILTER P ls  to  ls  *)
Theorem EL_EL_FILTER:
  !ls n P. n < LENGTH $ FILTER P ls
  ==> ?m. m < LENGTH ls /\ EL m ls = EL n $ FILTER P ls
    /\ n = m + (LENGTH $ FILTER P $ TAKE m ls) - (LENGTH $ TAKE m ls)
Proof
  Induct using SNOC_INDUCT
  >> rw[SNOC_APPEND]
  >> qmatch_goalsub_abbrev_tac `EL n $ FILTER P $ ls ++ [x]`
  >> Cases_on `n < LENGTH $ FILTER P ls`
  >- (
    first_x_assum $ drule_then strip_assume_tac
    >> qmatch_asmsub_rename_tac `m < LENGTH ls`
    >> qexists_tac `m`
    >> fs[EL_APPEND1,FILTER_APPEND_DISTRIB,TAKE_APPEND1]
  )
  >> gs[NOT_LESS,FILTER_APPEND_DISTRIB,EL_APPEND2]
  >> IF_CASES_TAC
  >> gs[]
  >> qexists_tac `LENGTH ls`
  >> gs[EL_APPEND2,FILTER_APPEND_DISTRIB,TAKE_APPEND1,LESS_OR_EQ]
QED

Theorem EL_FILTER_LENGTH_LT:
  !ls n P. n < LENGTH ls /\ P $ EL n ls
  ==> LENGTH $ FILTER P $ TAKE n ls < LENGTH $ FILTER P ls
Proof
  Induct >> rw[] >> Cases_on `n` >> fs[]
QED

Theorem LENGTH_FILTER_TAKE_LESS_SUC:
  !ls n P.
    LENGTH $ FILTER P $ TAKE n ls <= LENGTH $ FILTER P $ TAKE (SUC n) ls
    /\
      (n < LENGTH ls /\ P $ EL n ls ==>
      LENGTH $ FILTER P $ TAKE n ls < LENGTH $ FILTER P $ TAKE (SUC n) ls)
Proof
  fs[GSYM SNOC_EL_TAKE,SNOC_APPEND,FILTER_APPEND_DISTRIB]
  >> Induct >- fs[]
  >> gen_tac >> Cases >> rw[TAKE_def]
QED

Theorem FEVERY_FEVERY_FUPDATE:
  !env P var val.
  FEVERY (P o SND) env /\ P val
  ==> FEVERY (P o SND) (env |+ (var, val))
Proof
  fs[FEVERY_STRENGTHEN_THM,FEVERY_FEMPTY]
QED

Theorem FEVERY_MONOTONIC:
  !P Q l. FEVERY P l /\ (!x. P x ==> Q x) ==> FEVERY Q l
Proof
  fs[FEVERY_ALL_FLOOKUP]
QED

(* offset_none properties *****************************************************)

Theorem offset_none_eq:
  offset_none M t
  = t - ((LENGTH $ TAKE (PRE t) M) - (LENGTH $ FILTER IS_SOME $ TAKE (PRE t) M))
Proof
  fs[offset_none_def,LENGTH_FILTER_LEQ,SUB_SUB]
QED

Theorem offset_none_GT_ZERO:
  !M n x. oEL n M = SOME $ SOME x ==> 0 < offset_none M (SUC n)
Proof
  rw[oEL_THM,offset_none_def,LENGTH_FILTER_LEQ]
QED

Theorem some_zero_offset_none_APPEND_EQ:
  !M M' t. some_zero M t
  ==> offset_none (M ++ M') t = offset_none M t
Proof
  rw[offset_none_def,some_zero_def,is_some_some_def]
  >> fs[TAKE_APPEND1]
QED

Theorem offset_none_zero:
  !M. offset_none M 0 = 0
Proof
  fs[offset_none_def]
QED

Theorem offset_none_LESS_OR_EQ:
  !M t. offset_none M t <= t
Proof
  fs[offset_none_def,LENGTH_FILTER_LEQ]
QED

Theorem offset_none_GT_zero:
  !M t. is_some_some M t ==> 0 < offset_none M t
Proof
  fs[offset_none_def,is_some_some_def]
QED

Theorem offset_none_LESS_EQ_offset_none_SUC:
  !M a. offset_none M a <= offset_none M (SUC a)
Proof
  rpt gen_tac
  >> Cases_on `a < LENGTH M`
  >> fs[offset_none_def,LENGTH_TAKE,LENGTH_FILTER_TAKE_LESS_SUC]
  >> qmatch_goalsub_abbrev_tac `FILTER f $ TAKE (PRE a) M`
  >> qspecl_then [`M`,`PRE a`,`f`] assume_tac $ cj 1 LENGTH_FILTER_TAKE_LESS_SUC
  >> Cases_on `0 < a`
  >> gs[NOT_LESS,iffLR SUC_PRE]
  >> rev_dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >> gs[LENGTH_TAKE_EQ]
QED

Theorem offset_none_LESS_offset_none_SUC:
  !M a.
    is_some_some M a
    ==> offset_none M a < offset_none M (SUC a)
Proof
  REWRITE_TAC[offset_none_def,is_some_some_def]
  >> rpt gen_tac >> strip_tac
  >> imp_res_tac $ cj 2 LENGTH_FILTER_TAKE_LESS_SUC
  >> gs[iffLR SUC_PRE]
QED

Theorem offset_none_LESS_offset_none:
  !M a b.
    is_some_some M a /\ a < b
    ==> offset_none M a < offset_none M b
Proof
  rpt gen_tac
  >> Induct_on `b-a`
  >> rw[SUB_LEFT_EQ]
  >> Cases_on `v = 0`
  >- (
    REWRITE_TAC[GSYM ADD_SUC]
    >> fs[offset_none_LESS_offset_none_SUC]
  )
  >> irule LESS_LESS_EQ_TRANS
  >> first_x_assum $ drule_at_then Any $ irule_at Any
  >> REWRITE_TAC[GSYM ADD_SUC]
  >> irule_at Any offset_none_LESS_EQ_offset_none_SUC
  >> fs[NOT_ZERO_LT_ZERO]
QED

Theorem offset_none_LESS_eq':
  !M a b.
    is_some_some M a /\ is_some_some M b
    ==> (offset_none M a < offset_none M b <=> a < b)
Proof
  rw[EQ_IMP_THM,offset_none_LESS_offset_none]
  >> spose_not_then assume_tac
  >> gs[NOT_LESS,LESS_OR_EQ]
  >> imp_res_tac offset_none_LESS_offset_none
  >> fs[]
QED

Theorem offset_none_LESS_eq:
  !M a b.
    some_zero M a /\ some_zero M b
    ==> (offset_none M a < offset_none M b <=> a < b)
Proof
  rw[some_zero_def]
  >> imp_res_tac $ cj 1 $ iffLR is_some_some_def
  >> fs[offset_none_zero,offset_none_LESS_eq',offset_none_GT_zero]
QED

Theorem offset_none_EQ_LESS_OR_EQ:
  !M a b.
    some_zero M a /\ some_zero M b
    ==> (offset_none M a <= offset_none M b <=> a <= b)
Proof
  dsimp[LESS_OR_EQ,offset_none_LESS_eq,EQ_IMP_THM,DISJ_EQ_IMP]
  >> rw[NOT_LESS]
  >> gs[LESS_OR_EQ]
  >> drule_all $ iffRL offset_none_LESS_eq
  >> fs[]
QED

Theorem offset_none_inj:
  !M a b.
    some_zero M a /\ some_zero M b
    ==> (offset_none M a = offset_none M b <=> a = b)
Proof
  rw[EQ_IMP_THM] >> spose_not_then assume_tac
  >> dxrule_at_then Concl assume_tac $ iffRL EQ_LESS_EQ
  >> gs[NOT_LESS,LESS_OR_EQ]
  >> drule_all_then assume_tac $ iffRL offset_none_LESS_eq
  >> fs[]
QED

Triviality offset_none_COND:
  !cond M a b.
    (if cond then (offset_none M a) else (offset_none M b))
    = offset_none M (if cond then a else b)
Proof
  rw[]
QED

Theorem offset_none_COND0:
  !cond M a.
    (if cond then (offset_none M a) else 0)
    = offset_none M (if cond then a else 0)
Proof
  fs[GSYM offset_none_COND,offset_none_zero]
QED

Theorem offset_none_MAX_is_some_some:
  !M a b.
    is_some_some M a /\ is_some_some M b
    ==> (MAX (offset_none M a) (offset_none M b) = offset_none M (MAX a b))
Proof
  fs[MAX_DEF,offset_none_COND,offset_none_LESS_eq']
QED

Theorem some_zero_COND:
  !cond M a b. some_zero M a /\ some_zero M b
    ==> some_zero M $ if cond then a else b
Proof
  rw[]
QED

Theorem some_zero_COND0:
  !cond M a b. some_zero M a
    ==> some_zero M $ if cond then a else 0
Proof
  rw[]
QED

Theorem some_zero_MAX:
  !M a b. some_zero M a /\ some_zero M b ==> some_zero M $ MAX a b
Proof
  rw[MAX_DEF]
QED

Theorem offset_none_MAX:
  !M a b.
    some_zero M a /\ some_zero M b
    ==> (MAX (offset_none M a) (offset_none M b) = offset_none M (MAX a b))
Proof
  dsimp[some_zero_def,offset_none_zero,offset_none_MAX_is_some_some]
QED


(* mem_get, mem_read, mem_is_* and offset and some_zero ***********************)

Theorem mem_get_mem_is_loc_mem_is_cid:
  !t M l x. 0 < t /\
  mem_get M l t = SOME x ==> mem_is_loc M t x.loc /\ mem_is_cid M t x.cid
Proof
  rpt strip_tac
  >> gs[mem_get_PRE,mem_is_loc_PRE,mem_is_cid_PRE,AllCaseEqs()]
QED

Theorem mem_get_offset_none:
  !t M k l x.
  mem_get M l t = SOME x
  ==> mem_get (FILTER IS_SOME M) l (offset_none M t) = SOME x
Proof
  Cases >> rpt gen_tac
  >> fs[mem_get_def,mem_get_PRE,offset_none_zero,AllCaseEqs(),PULL_EXISTS,offset_none_GT_ZERO,oEL_THM]
  >> strip_tac
  >> drule_then (qspec_then `IS_SOME` assume_tac) EL_FILTER
  >> gs[offset_none_def]
  >> qmatch_asmsub_abbrev_tac `EL m $ FILTER _ _`
  >> qmatch_goalsub_abbrev_tac `EL mm $ FILTER _ _`
  >> `mm = m` by (unabbrev_all_tac >> decide_tac)
  >> pop_assum $ fs o single
  >> unabbrev_all_tac
  >> fs[EL_FILTER_LENGTH_LT]
QED

Theorem mem_get_some_zero:
  !t M l x.
    mem_get M l t = SOME x ==> some_zero M t
Proof
  Cases >> rpt gen_tac
  >> fs[mem_get_def,AllCaseEqs(),oEL_THM,some_zero_def,is_some_some_def]
QED

Theorem mem_read_offset_none:
  !t M k l x.
  mem_read M l t = SOME x
  ==> mem_read (FILTER IS_SOME M) l (offset_none M t) = SOME x
Proof
  rw[mem_read_def]
  >> BasicProvers.every_case_tac
  >> imp_res_tac mem_get_offset_none
  >> gs[]
QED

Theorem mem_read_some_zero:
  !t M l x.
    mem_read M l t = SOME x ==> some_zero M t
Proof
  Cases >> rw[mem_read_def,AllCaseEqs()]
  >> imp_res_tac mem_get_some_zero
QED

Theorem mem_is_loc_some_zero:
  !t M cid.
    mem_is_loc M t cid ==> some_zero M t
Proof
  Cases >> rw[mem_is_loc_def]
  >> BasicProvers.every_case_tac
  >> gs[oEL_THM,some_zero_def,is_some_some_def]
QED

Theorem is_some_some_EXISTS_offset_none:
  !M t. is_some_some (FILTER IS_SOME M) t
  ==> ?t'. t = offset_none M t'
    /\ is_some_some M t'
Proof
  rw[is_some_some_def,offset_none_def]
  >> drule_then strip_assume_tac EL_EL_FILTER
  >> qmatch_asmsub_rename_tac `m < LENGTH M`
  >> qexists_tac `SUC m`
  >> gs[TAKE_LENGTH_ID_rwt2]
QED

Theorem mem_is_loc_offset_none:
  !t M l.
  mem_is_loc M t l
  <=> (mem_is_loc (FILTER IS_SOME M) (offset_none M t) l /\ some_zero M t)
Proof
  rw[GSYM mem_get_is_loc,EQ_IMP_THM,optionTheory.IS_SOME_EXISTS,PULL_EXISTS]
  >- (
    drule_then (irule_at Any) mem_get_offset_none
    >> imp_res_tac mem_get_some_zero
  )
  >> gs[some_zero_def,offset_none_zero,mem_get_def,mem_get_PRE,offset_none_GT_zero]
  >> imp_res_tac $ cj 1 $ iffLR is_some_some_def
  >> BasicProvers.every_case_tac
  >> gvs[mem_get_PRE,oEL_THM,is_some_some_def]
  >> rev_drule_then drule EL_FILTER
  >> disch_then $ REWRITE_TAC o single o GSYM
  >> REWRITE_TAC[offset_none_def]
  >> qmatch_goalsub_abbrev_tac `EL m _`
  >> qmatch_asmsub_abbrev_tac `EL mm _`
  >> `m = mm` by (
    unabbrev_all_tac
    >> REWRITE_TAC[offset_none_def]
    >> decide_tac
  )
  >> fs[]
QED

Theorem mem_is_cid_offset_none:
  !t M l.
  some_zero M t
  ==> mem_is_cid M t l = mem_is_cid (FILTER IS_SOME M) (offset_none M t) l
Proof
  Cases >- fs[offset_none_zero,mem_is_cid_def]
  >> rw[some_zero_def,mem_is_cid_PRE,offset_none_GT_zero,offset_none_def,is_some_some_def]
  >> Cases_on `n`
  >- (Cases_on `M` >> fs[oEL_THM])
  >> drule_all_then assume_tac $ GSYM EL_FILTER
  >> qmatch_goalsub_abbrev_tac `oEL m $ FILTER IS_SOME M`
  >> qmatch_asmsub_abbrev_tac `EL mm $ FILTER IS_SOME M`
  >> `m = mm` by (unabbrev_all_tac >> fs[])
  >> pop_assum $ fs o single
  >> fs[oEL_THM]
QED

(* shifting times of a state **************************************************)

Definition timeshift_def:
  timeshift f s =
    s with <|
      bst_viewenv updated_by (λenv. f o_f env);
      bst_coh := f o s.bst_coh;
      bst_v_rOld := f s.bst_v_rOld;
      bst_v_wOld := f s.bst_v_wOld;
      bst_v_rNew := f s.bst_v_rNew;
      bst_v_wNew := f s.bst_v_wNew;
      bst_v_Rel := f s.bst_v_Rel;
      bst_v_CAP := f s.bst_v_CAP;
      bst_xclb :=
        OPTION_MAP (λx. x with <|
          xclb_time updated_by f; xclb_view updated_by f
        |>) s.bst_xclb;
      bst_fwdb :=
        λl. s.bst_fwdb l with <|
          fwdb_time updated_by f; fwdb_view updated_by f
        |>; (* fwdb_t_accfupds *)
      bst_prom := MAP f s.bst_prom
    |>
End

Theorem timeshift_simps:
  (timeshift f s).bst_pc = s.bst_pc
  /\ (timeshift f s).bst_environ = s.bst_environ
  /\ timeshift I s = s
Proof
  fs[timeshift_def]
  >> fs[FUN_EQ_THM,bir_state_t_component_equality,fwdb_t_component_equality,o_f_id,I_EQ_IDABS]
  >> qmatch_goalsub_rename_tac `s.bst_xclb`
  >> Cases_on `s.bst_xclb`
  >> fs[optionTheory.OPTION_MAP_DEF,xclb_t_component_equality]
  >> rpt $ irule_at Any EQ_REFL
QED


(* xclfail_update_* invariants ************************************************)

Theorem xclfail_update_env_timeshift:
  xclfail_update_env p (timeshift f s) = xclfail_update_env p s
Proof
  fs[timeshift_def,bir_state_t_component_equality,xclfail_update_env_def]
QED

Theorem xclfail_update_viewenv_f_o_f:
  !f p s viewenv. xclfail_update_viewenv p s = SOME viewenv
  /\ f 0 = 0
  ==> xclfail_update_viewenv p (timeshift f s)
    = SOME (f o_f viewenv)
Proof
  rpt strip_tac
  >> fs[Once xclfail_update_viewenv_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> rw[timeshift_def,xclfail_update_viewenv_def]
  >> fs[o_f_FUPDATE]
QED

Theorem xclfail_update_viewenv_FEVERY:
  !f p s viewenv. xclfail_update_viewenv p s = SOME viewenv
  /\ FEVERY (f o SND) s.bst_viewenv
  /\ f 0
  ==> FEVERY (f o SND) viewenv
Proof
  rpt strip_tac
  >> fs[Once xclfail_update_viewenv_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> rw[xclfail_update_viewenv_def]
  >> drule_all_then irule FEVERY_FEVERY_FUPDATE
QED

(* fulfil_update_* invariants *************************************************)

Theorem fulfil_update_env_timeshift:
  !f benv p s xcl. fulfil_update_env p s xcl = SOME benv
  ==> fulfil_update_env p (timeshift f s) xcl = SOME benv
Proof
  gen_tac >> Cases >> rpt gen_tac
  >> fs[Once fulfil_update_env_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> rw[timeshift_def,fulfil_update_env_def]
QED

Theorem fulfil_update_viewenv_timeshift:
  !f p s xcl t new_viewenv.
  fulfil_update_viewenv p s xcl t = SOME new_viewenv
  ==> fulfil_update_viewenv p (timeshift f s) xcl (f t)
    = SOME $ f o_f new_viewenv
Proof
  reverse $ rw[Once fulfil_update_viewenv_def]
  >- fs[fulfil_update_viewenv_def,timeshift_def]
  >> BasicProvers.every_case_tac
  >> gvs[fulfil_update_viewenv_def,timeshift_def]
QED

Theorem FEVERY_fulfil_update_viewenv:
  FEVERY (f o SND) s.bst_viewenv
  /\ fulfil_update_viewenv p s xcl t = SOME viewenv
  /\ f t
  ==> FEVERY (f o SND) viewenv
Proof
  rw[fulfil_update_viewenv_def]
  >> gvs[AllCaseEqs(),FEVERY_FEVERY_FUPDATE]
QED

(* bir_eval_view_of_exp invariants ********************************************)

Theorem bir_exec_stmtB_mix_timeshift:
  !b s s' genv genv' oo f.
  bir_exec_stmtB_mix b (timeshift f s) genv
  = (FST $ bir_exec_stmtB_mix b s genv,
      timeshift f $ FST $ SND $ bir_exec_stmtB_mix b s genv,
      SND $ SND $ bir_exec_stmtB_mix b s genv)
Proof
  Cases
  >> rw[bir_exec_stmtB_mix_def,bir_exec_stmt_assign_mix_def,bir_exec_stmt_observe_mix_def,bir_exec_stmt_assume_mix_def,bir_exec_stmt_fence_def,timeshift_simps,bir_exec_stmt_assert_mix_def]
  >> BasicProvers.every_case_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,timeshift_def,bir_state_set_typeerror_def,bir_state_t_component_equality]
QED

Theorem bir_exec_stmtE_mix_timeshift:
  !e p s s' f.
  bir_exec_stmtE p e s = s'
  ==> bir_exec_stmtE p e (timeshift f s) = timeshift f s'
Proof
  Cases
  >> rw[bir_exec_stmtE_def,bir_exec_stmt_halt_def,bir_exec_stmt_jmp_def,bir_exec_stmt_cjmp_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,timeshift_def,bir_state_set_typeerror_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem bir_exec_stmt_mix_timeshift:
  !e p s s' genv genv' oo f.
  bir_exec_stmt_mix p e (timeshift f s) genv
    = (FST $ bir_exec_stmt_mix p e s genv,
      timeshift f $ FST $ SND $ bir_exec_stmt_mix p e s genv,
      SND $ SND $ bir_exec_stmt_mix p e s genv)
Proof
  Cases
  >> rw[bir_exec_stmt_mix_def,bir_exec_stmtE_mix_timeshift,pairTheory.ELIM_UNCURRY]
  >> fs[bir_exec_stmtB_mix_timeshift]
  >> fs[bir_state_is_terminated_def,timeshift_def]
QED

Theorem bir_eval_view_of_exp_some_zero:
  !M viewenv a_e.
  FEVERY (some_zero M o SND) viewenv
  ==> some_zero M $ bir_eval_view_of_exp a_e viewenv
Proof
  fs[GSYM PULL_FORALL]
  >> rpt gen_tac >> strip_tac
  >> Induct
  >> rw[bir_eval_view_of_exp_def,some_zero_MAX]
  >> BasicProvers.every_case_tac
  >> fs[]
  >> imp_res_tac FEVERY_FLOOKUP >> fs[]
QED

Theorem bir_eval_view_of_exp_offset_none:
  !a_e v_addr viewenv M.
    bir_eval_view_of_exp a_e viewenv = v_addr
    /\ FEVERY (some_zero M o SND) viewenv
    ==> bir_eval_view_of_exp a_e ((offset_none M) o_f viewenv) = offset_none M v_addr
Proof
  Induct
  >> fs[bir_eval_view_of_exp_def,FLOOKUP_o_f,offset_none_zero,bir_eval_view_of_exp_some_zero,offset_none_MAX]
  >> rw[MAX_DEF,offset_none_def]
  >> BasicProvers.every_case_tac >> fs[]
QED

Theorem bir_eval_view_of_exp_offset_none_FUPDATE:
  !viewenv upd var M a_e v_addr.
  FEVERY (some_zero M o SND) viewenv /\ some_zero M upd
  /\ bir_eval_view_of_exp a_e (viewenv |+ (var,upd)) = v_addr
  ==> bir_eval_view_of_exp a_e (offset_none M o_f viewenv |+ (var, offset_none M upd)) = offset_none M v_addr
Proof
  rpt strip_tac
  >> ONCE_REWRITE_TAC[GSYM o_f_FUPDATE]
  >> fs[FEVERY_FEVERY_FUPDATE,bir_eval_view_of_exp_offset_none]
QED

Theorem bir_eval_view_of_exp_some_zero_FUPDATE:
  !viewenv var upd M a_e.
  FEVERY (some_zero M o SND) viewenv
  /\ some_zero M upd
  ==> some_zero M $ bir_eval_view_of_exp a_e (viewenv |+ (var, upd))
Proof
  fs[GSYM PULL_FORALL]
  >> rpt gen_tac >> strip_tac
  >> Induct
  >> rw[bir_eval_view_of_exp_def,some_zero_COND,some_zero_MAX,FLOOKUP_UPDATE]
  >> BasicProvers.every_case_tac >> fs[some_zero_zero]
  >> imp_res_tac FEVERY_FLOOKUP
  >> fs[]
QED

(* time_constraints and invariants ********************************************)

Definition time_constraints_def:
   time_constraints f s <=>
      FEVERY (f o SND) s.bst_viewenv
      /\ (!l. f $ s.bst_coh l)
      /\ f s.bst_v_rOld
      /\ f s.bst_v_wOld
      /\ f s.bst_v_rNew
      /\ f s.bst_v_wNew
      /\ f s.bst_v_Rel
      /\ f s.bst_v_CAP
      /\ EVERY f s.bst_prom
      /\ (IS_SOME s.bst_xclb ==> (λx.
        f x.xclb_time /\ f x.xclb_view) $ THE s.bst_xclb)
      /\ (!l. f (s.bst_fwdb l).fwdb_view /\ f (s.bst_fwdb l).fwdb_time)
End

Theorem time_constraints_offset_none_APPEND_EQ:
  !M M' s. time_constraints (some_zero M) s
  ==> timeshift (offset_none $ M ++ M') s = timeshift (offset_none M) s
Proof
  rw[time_constraints_def,timeshift_def]
  >> fs[bir_state_t_component_equality,some_zero_offset_none_APPEND_EQ,combinTheory.o_DEF,FUN_EQ_THM,MAP_EQ_f,EVERY_MEM]
  >> drule_then assume_tac FEVERY_FLOOKUP
  >> irule_at Any o_f_cong
  >> irule_at Any optionTheory.OPTION_MAP_CONG
  >> fs[some_zero_offset_none_APPEND_EQ,FRANGE_FLOOKUP,xclb_t_component_equality,fwdb_t_component_equality,optionTheory.IS_SOME_EXISTS,PULL_EXISTS]
QED

Theorem time_constraints_APPEND:
  !M M' s. time_constraints (some_zero M) s
  ==> time_constraints (some_zero $ M ++ M') s
Proof
  rw[]
  >> fs[time_constraints_def,some_zero_APPEND]
  >> drule_then (irule_at Any) FEVERY_MONOTONIC
  >> drule_at_then Any (irule_at Any) EVERY_MONOTONIC
  >> fs[combinTheory.o_DEF,some_zero_APPEND]
QED

Theorem bir_exec_stmt_mix_time_constraints:
  !stm f p s genv oo s2 genv'.
    bir_exec_stmt_mix p stm s genv = (oo,s2,genv')
    /\ time_constraints f s
    ==> time_constraints f s2
Proof
  ntac 2 Induct
  >> rw[bir_exec_stmt_mix_def,bir_exec_stmtB_mix_def,bir_exec_stmt_assign_mix_def,bir_exec_stmt_observe_mix_def,bir_exec_stmt_assume_mix_def,bir_exec_stmt_fence_def,timeshift_simps,bir_exec_stmt_assert_mix_def,bir_exec_stmtE_def,bir_exec_stmt_halt_def,bir_exec_stmt_jmp_def,bir_exec_stmt_cjmp_def]
  >> BasicProvers.every_case_tac
  >> fs[time_constraints_def,bir_exec_stmt_jmp_to_label_def,timeshift_def,bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def,bir_state_set_typeerror_def,bir_state_t_component_equality]
  >> BasicProvers.every_case_tac
  >> gvs[]
QED

(******************************************************************************)
(* Bisimulation main properties ***********************************************)
(******************************************************************************)

Definition drop_none_rel_def:
  drop_none_rel s M s' M' <=>
    M' = FILTER IS_SOME M /\ s' = timeshift (offset_none M) s
    /\ time_constraints (some_zero M) s
End

Theorem clstep_timeshift:
  !p cid s M genv prom s' genv'.
  clstep p cid s M genv prom s' genv'
  /\ time_constraints (some_zero M) s
  ==>
    clstep p cid (timeshift (offset_none M) s) (FILTER IS_SOME M) genv (MAP (offset_none M) prom) (timeshift (offset_none M) s') genv'
    /\ time_constraints (some_zero M) s'
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac clstep_ind
  >> conj_tac
  (* read *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> qpat_x_assum `v_pre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_post = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> imp_res_tac mem_read_some_zero
    >> imp_res_tac mem_read_offset_none
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` $ assume_tac o GSYM
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> drule_at Any bir_eval_view_of_exp_offset_none
    >> disch_then $ drule_then assume_tac
    >> `some_zero M v_addr` by (
      unabbrev_all_tac
      >> qpat_x_assum `_ = v_addr` $ fs o single o GSYM
      >> fs[bir_eval_view_of_exp_some_zero]
    )
    >> `some_zero M $ mem_read_view (s.bst_fwdb l) t` by
      fs[time_constraints_def,mem_read_view_def,some_zero_COND]
    >> `some_zero M v_post` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_COND,some_zero_MAX,some_zero_zero]
      >> fs[iffLR time_constraints_def]
    )
    >> `some_zero M v_pre` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_COND,some_zero_MAX,some_zero_zero]
      >> fs[iffLR time_constraints_def]
    )
    >> reverse conj_asm2_tac
    (* time_constraints *)
    >- (
      fs[time_constraints_def,FEVERY_FEVERY_FUPDATE]
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_MAX,some_zero_COND]
      >> gs[time_constraints_def]
      >> rw[]
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_MAX,some_zero_COND]
      >> fs[]
    )
    >> gvs[]
    >> irule $ cj 1 clstep_rules
    >> qhdtm_assum `mem_read` $ irule_at Any
    >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM]
    >> conj_tac
    (* ~mem_is_loc *)
    >- (
      gen_tac
      >> simp[AC DISJ_ASSOC DISJ_COMM]
      >> qmatch_goalsub_rename_tac `offset_none M t < t'`
      >> qmatch_goalsub_abbrev_tac `offset_none M t < t' /\ disj /\ _`
      >> strip_tac
      >> `is_some_some (FILTER IS_SOME M) t'` by (
        dxrule_then strip_assume_tac $ iffLR some_zero_def
        >> gs[]
      )
      >> dxrule_then strip_assume_tac is_some_some_EXISTS_offset_none
      >> qmatch_assum_rename_tac `is_some_some M t''`
      >> last_x_assum $ qspec_then `t''` (mp_tac o ONCE_REWRITE_RULE[mem_is_loc_offset_none])
      >> imp_res_tac $ cj 2 $ REWRITE_RULE[DISJ_IMP_THM] $ iffRL some_zero_def
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero]
      >> unabbrev_all_tac
      >> fs[]
    )
    >> conj_tac
    (* FLOOKUP_UPDATE *)
    >- (
      unabbrev_all_tac
      >> rpt $ AP_TERM_TAC ORELSE AP_THM_TAC
      >> simp[mem_read_view_def]
      >> gs[offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero]
      >> fs[offset_none_inj,COND_CONG]
    )
    >> qmatch_goalsub_abbrev_tac `mem_read_view offset_bst_fwdb (offset_none M t)`
    >> `mem_read_view offset_bst_fwdb (offset_none M t)
      = offset_none M $ mem_read_view (s.bst_fwdb l) t` by (
      qunabbrev_tac `offset_bst_fwdb`
      >> fs[mem_read_view_def,offset_none_COND,offset_none_inj]
    )
    >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND0,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,COND_CONG,offset_none_inj]
    >> conj_tac (* nested if-MAX-if *)
    >- (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_MAX,some_zero_COND,some_zero_COND0]
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND0,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,COND_CONG,offset_none_inj]
    )
    >> conj_tac (* nested if-MAX-if *)
    >- (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_MAX,some_zero_COND,some_zero_COND0]
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND0,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,COND_CONG,offset_none_inj]
    )
    >> conj_tac (* nested if-MAX *)
    >- (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_MAX,some_zero_COND,some_zero_COND0]
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND0,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,COND_CONG,offset_none_inj]
    )
    >> unabbrev_all_tac
    (* nested OPTION_MAP-if *)
    >> BasicProvers.every_case_tac
    >> fs[]
  )
  >> conj_tac
  (* xcl fail *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> gvs[]
    >> irule_at Any $ cj 2 clstep_rules
    >> drule_then (qspec_then `offset_none M` assume_tac) $ GSYM xclfail_update_viewenv_f_o_f
    >> fs[timeshift_simps,xclfail_update_env_timeshift,offset_none_zero,time_constraints_def]
    >> simp[timeshift_def,bir_state_t_component_equality]
    >> irule $ GSYM xclfail_update_viewenv_FEVERY
    >> fs[some_zero_zero]
    >> irule_at Any EQ_REFL
    >> fs[]
  )
  >> conj_tac
  (* write *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> qpat_x_assum `v_pre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> imp_res_tac mem_get_some_zero
    >> imp_res_tac mem_get_offset_none
    >> rpt $ qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> drule_at Any bir_eval_view_of_exp_offset_none
    >> disch_then (fn thm =>
      drule_at_then Any assume_tac thm
      >> rev_drule_at_then Any assume_tac thm)
    >> `some_zero M v_data` by (
      unabbrev_all_tac
      >> qpat_x_assum `_ = v_data` $ fs o single o GSYM
      >> fs[bir_eval_view_of_exp_some_zero]
    )
    >> `some_zero M v_addr` by (
      unabbrev_all_tac
      >> qpat_x_assum `_ = v_addr` $ fs o single o GSYM
      >> fs[bir_eval_view_of_exp_some_zero]
    )
    >> `some_zero M $ get_xclb_view s.bst_xclb` by (
      Cases_on `s.bst_xclb`
      >> fs[get_xclb_view_def,time_constraints_def,some_zero_zero]
    )
    >> `some_zero M v_pre` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_COND,some_zero_MAX,some_zero_zero]
      >> fs[iffLR time_constraints_def]
    )
    >> reverse conj_asm2_tac
    (* time_constraints *)
    >- (
      qpat_x_assum `_ = fulfil_update_viewenv _ _ _ _` $ assume_tac o GSYM
      >> simp[time_constraints_def]
      >> drule_at_then Any (irule_at Any) FEVERY_fulfil_update_viewenv
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,FILTER_MAP,MEM_MAP_f,EVERY_FILTER_IMP]
      >> rw[some_zero_MAX]
    )
    >> irule $ cj 3 clstep_rules
    >> drule_then (irule_at Any) $ GSYM fulfil_update_viewenv_timeshift
    >> drule_then (irule_at Any) $ GSYM fulfil_update_env_timeshift
    >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,FILTER_MAP,MEM_MAP_f,EVERY_FILTER_IMP]
    >> qmatch_goalsub_abbrev_tac `MAP _ l1 = MAP _ l2`
    >> `l1 = l2` by (
      unabbrev_all_tac
      >> fs[EVERY_MEM]
      >> rw[FILTER_EQ,offset_none_inj]
    )
    >> pop_assum $ fs o single
    >> qmatch_goalsub_abbrev_tac `xcl ==> Atomic`
    >> `xcl ==> Atomic` by (
      rw[Abbr`Atomic`,fulfil_atomic_ok_def]
      >> fs[fulfil_atomic_ok_def]
      >> qmatch_assum_abbrev_tac `mem_is_loc M (THE b).xclb_time l ==> _`
      >> `mem_is_loc M (THE b).xclb_time l` by (
        Cases_on`s.bst_xclb` >- fs[]
        >> unabbrev_all_tac
        >> irule $ iffRL mem_is_loc_offset_none
        >> gvs[]
      )
      >> qunabbrev_tac `b`
      >> qmatch_goalsub_rename_tac `mem_is_cid _ t' _`
      >> qpat_x_assum `mem_is_loc (FILTER IS_SOME M) t' l` assume_tac
      >> drule_then assume_tac mem_is_loc_some_zero
      >> drule_then strip_assume_tac $ iffLR some_zero_def >> fs[]
      >> drule_then strip_assume_tac is_some_some_EXISTS_offset_none
      >> asm_rewrite_tac[]
      >> irule $ REWRITE_RULE[AND_IMP_INTRO] $ iffLR mem_is_cid_offset_none
      >> conj_asm1_tac >- simp[some_zero_def]
      >> first_x_assum irule
      >> Cases_on `s.bst_xclb` >> fs[]
      >> irule_at Any $ iffRL mem_is_loc_offset_none
      >> gs[offset_none_LESS_eq]
    )
    >> pop_assum $ fs o single
    >> qmatch_goalsub_abbrev_tac `get_xclb_view offset_b`
    >> `get_xclb_view offset_b = offset_none M $ get_xclb_view s.bst_xclb` by (
      qunabbrev_tac `offset_b`
      >> Cases_on `s.bst_xclb`
      >> rw[get_xclb_view_def,offset_none_zero]
    )
    >> pop_assum $ REWRITE_TAC o single
    >> unabbrev_all_tac
    >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,FILTER_MAP,MEM_MAP_f,EVERY_FILTER_IMP]
    (* fwdb and OPTION_MAP *)
    >> rw[]
  )
  >> conj_tac
  (* amo *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> qpat_x_assum `v_rPre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_rPost = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_wPre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> imp_res_tac mem_get_some_zero
    >> imp_res_tac mem_get_offset_none
    >> imp_res_tac mem_read_some_zero
    >> imp_res_tac mem_read_offset_none
    >> rpt $ qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` $ assume_tac o GSYM
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> drule_at Any bir_eval_view_of_exp_offset_none
    >> disch_then (fn thm =>
      drule_at_then Any assume_tac thm
      >> rev_drule_at_then Any assume_tac thm)
    >> `some_zero M v_addr` by (
      unabbrev_all_tac
      >> qpat_x_assum `_ = v_addr` $ fs o single o GSYM
      >> fs[bir_eval_view_of_exp_some_zero]
    )
    >> `some_zero M (mem_read_view (s.bst_fwdb l) t_r)` by
      fs[time_constraints_def,mem_read_view_def,some_zero_COND]
    >> `some_zero M v_rPost` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_COND,some_zero_COND0,some_zero_MAX]
      >> fs[time_constraints_def,some_zero_zero]
    )
    >> `some_zero M v_data` by (
      qpat_x_assum `_ = v_data` $ fs o single o GSYM
      >> fs[time_constraints_def,some_zero_zero,bir_eval_view_of_exp_some_zero_FUPDATE]
    )
    >> `some_zero M v_wPre /\ some_zero M v_rPre` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[some_zero_COND,some_zero_COND0,some_zero_MAX]
      >> gs[time_constraints_def,some_zero_zero]
    )
    >> reverse conj_asm2_tac
    (* time_constraints *)
    >- (
      simp[time_constraints_def]
      >> drule_at_then Any (irule_at Any) FEVERY_FEVERY_FUPDATE
      >> gs[time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_state_t_component_equality,bir_eval_exp_view_def,FUN_EQ_THM,FILTER_MAP,MEM_MAP_f,EVERY_FILTER_IMP,combinTheory.APPLY_UPDATE_THM]
      >> rw[some_zero_MAX]
    )
    >> irule $ cj 4 clstep_rules
    >> qhdtm_assum `mem_read` $ irule_at Any
    >> qhdtm_assum `mem_get` $ irule_at Any
    >> simp[bir_state_t_component_equality]
    >> qmatch_goalsub_abbrev_tac `mem_read_view offset_bst_fwdb (offset_none M t_r)`
    >> `mem_read_view offset_bst_fwdb (offset_none M t_r)
      = offset_none M $ mem_read_view (s.bst_fwdb l) t_r` by (
      qunabbrev_tac `offset_bst_fwdb`
      >> gs[time_constraints_def,mem_read_view_def,offset_none_COND,offset_none_inj,timeshift_def]
    )
    >> pop_assum $ REWRITE_TAC o single
    >> qunabbrev_tac `offset_bst_fwdb`
    >> gs[iffLR time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,timeshift_def,bir_eval_exp_view_def,FUN_EQ_THM,FILTER_MAP,combinTheory.APPLY_UPDATE_THM,MEM_MAP_f]
    >> conj_tac
    (* ~mem_is_loc *)
    >- (
      gen_tac
      >> qmatch_goalsub_rename_tac `offset_none M t_r < t'`
      >> strip_tac
      >> `is_some_some (FILTER IS_SOME M) t'` by (
        dxrule_then strip_assume_tac $ iffLR some_zero_def
        >> gs[]
      )
      >> dxrule_then strip_assume_tac is_some_some_EXISTS_offset_none
      >> qmatch_assum_rename_tac `is_some_some M t''`
      >> last_x_assum $ qspec_then `t''` (mp_tac o ONCE_REWRITE_RULE[mem_is_loc_offset_none])
      >> imp_res_tac $ cj 2 $ REWRITE_RULE[DISJ_IMP_THM] $ iffRL some_zero_def
      >> gs[iffLR time_constraints_def,offset_none_LESS_eq,offset_none_EQ_LESS_OR_EQ,offset_none_COND0,offset_none_COND,offset_none_MAX,offset_none_zero,some_zero_COND,some_zero_MAX,some_zero_zero,MEM_MAP_f]
    )
    >> qmatch_goalsub_abbrev_tac `_ |+ (var, offset_v_rPost)`
    >> `offset_v_rPost = offset_none M v_rPost` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[offset_none_COND0,offset_none_COND,offset_none_MAX,some_zero_COND,some_zero_MAX]
      >> fs[some_zero_zero,time_constraints_def]
    )
    >> pop_assum $ REWRITE_TAC o single
    >> qunabbrev_tac `offset_v_rPost`
    >> qmatch_goalsub_abbrev_tac `MAP _ l1 = MAP _ l2`
    >> `l1 = l2` by (
      unabbrev_all_tac
      >> fs[time_constraints_def,EVERY_MEM]
      >> rw[FILTER_EQ,offset_none_inj]
    )
    >> pop_assum $ fs o single
    >> map_every qunabbrev_tac [`l1`,`l2`]
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[bir_state_t_accfupds]
    >> ONCE_REWRITE_TAC[GSYM o_f_FUPDATE]
    >> rev_drule_at_then (Pos $ el 2) assume_tac bir_eval_view_of_exp_offset_none
    >> fs[]
    >> pop_assum kall_tac
    >> rpt $ irule_at Any $ GSYM offset_none_MAX
    >> qmatch_goalsub_abbrev_tac `offset_none M $ MAX A _ = MAX A' _`
    >> `A' = offset_none M A /\ some_zero M A` by (
      map_every qunabbrev_tac [`A`,`A'`,`v_rPost`,`v_rPre`]
      >> fs[iffLR time_constraints_def,offset_none_zero,GSYM offset_none_MAX,GSYM offset_none_COND,GSYM some_zero_COND,GSYM some_zero_MAX]
    )
    >> fs[iffLR time_constraints_def,offset_none_MAX,offset_none_LESS_eq]
    >> irule_at Any $ REWRITE_RULE[AND_IMP_INTRO] $ iffRL offset_none_LESS_eq
    >> unabbrev_all_tac
    >> fs[iffLR time_constraints_def,some_zero_COND,some_zero_COND0,some_zero_zero,some_zero_MAX]
    (* fwdb *)
    >> rw[]
    >> dep_rewrite.DEP_REWRITE_TAC[offset_none_MAX,offset_none_COND,some_zero_COND,some_zero_COND0,some_zero_zero,some_zero_MAX]
    >> ONCE_REWRITE_TAC[GSYM o_f_FUPDATE]
    >> dep_rewrite.DEP_REWRITE_TAC $ single $ SIMP_RULE (srw_ss()) [] bir_eval_view_of_exp_offset_none
    >> dep_rewrite.DEP_REWRITE_TAC[offset_none_MAX]
    >> gs[iffLR time_constraints_def]
  )
  >> conj_tac
  (* fence *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> reverse conj_asm2_tac
    >- fs[time_constraints_def,some_zero_MAX,some_zero_zero,some_zero_COND,some_zero_COND0]
    >> fs[]
    >> irule $ cj 5 clstep_rules
    >> simp[timeshift_def,bir_state_t_component_equality]
    >> dep_rewrite.DEP_REWRITE_TAC[offset_none_zero,offset_none_MAX,offset_none_COND,offset_none_COND0,some_zero_COND,some_zero_COND0,some_zero_MAX]
    >> gs[time_constraints_def,some_zero_zero]
  )
  >> conj_tac
  (* branch *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[bir_eval_exp_view_def]
    >> drule_all_then assume_tac bir_eval_view_of_exp_offset_none
    >> reverse conj_asm2_tac
    >- (
      simp[time_constraints_def]
      >> irule_at Any some_zero_MAX
      >> drule_all_then assume_tac bir_exec_stmt_mix_time_constraints
      >> qpat_x_assum `bir_eval_view_of_exp _ _ = v_addr` $ assume_tac o GSYM
      >> fs[time_constraints_def,bir_eval_view_of_exp_some_zero]
    )
    >> irule_at Any $ cj 6 clstep_rules
    >> drule_then assume_tac bir_eval_view_of_exp_some_zero
    >> gvs[timeshift_simps,bir_exec_stmt_mix_timeshift,bir_eval_exp_view_def]
    >> simp[timeshift_def,bir_state_t_component_equality]
    >> fs[time_constraints_def,offset_none_MAX]
  )
  >> conj_tac
  (* expr *)
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[bir_eval_exp_view_def]
    >> drule_then assume_tac bir_eval_view_of_exp_some_zero
    >> drule_all_then (assume_tac o GSYM) $ GSYM bir_eval_view_of_exp_offset_none
    >> reverse conj_asm2_tac
    >- (
      simp[time_constraints_def]
      >> drule_then (irule_at Any) FEVERY_FEVERY_FUPDATE
      >> gs[time_constraints_def]
    )
    >> irule $ cj 7 clstep_rules
    >> simp[bir_eval_exp_view_def,timeshift_def,bir_state_t_component_equality]
    >> irule_at Any EQ_REFL
    >> fs[]
  )
  (* generic *)
  >> (
    rpt gen_tac >> ntac 2 strip_tac
    >> fs[]
    >> irule_at Any $ cj 8 clstep_rules
    >> simp[timeshift_simps,bir_exec_stmt_mix_timeshift]
    >> drule_all_then irule bir_exec_stmt_mix_time_constraints
  )
QED

Theorem cstep_timeshift:
  !p cid s M genv prom s' M' genv'.
  cstep p cid s M genv prom s' M' genv'
  /\ time_constraints (some_zero M) s
  ==>
    cstep p cid (timeshift (offset_none M) s) (FILTER IS_SOME M) genv
      (MAP (offset_none M') prom) (timeshift (offset_none M') s') (FILTER IS_SOME M') genv'
    /\ time_constraints (some_zero M') s'
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac cstep_ind
  >> conj_tac
  >- (
    rpt gen_tac >> ntac 2 strip_tac
    >> drule_all_then strip_assume_tac clstep_timeshift
    >> fs[cstep_cases]
  )
  >> rpt gen_tac >> ntac 2 strip_tac
  >> reverse conj_tac
  >- (
    fs[time_constraints_def,some_zero_APPEND]
    >> drule_then (irule_at Any) FEVERY_MONOTONIC
    >> drule_at_then Any (irule_at Any) EVERY_MONOTONIC
    >> fs[combinTheory.o_DEF,some_zero_APPEND,pairTheory.ELIM_UNCURRY]
    >> simp[some_zero_def,is_some_some_def,EL_APPEND2]
    >> qmatch_goalsub_abbrev_tac `EL m`
    >> `m = 0` by (unabbrev_all_tac >> decide_tac)
    >> fs[]
  )
  >> dsimp[cstep_cases,FILTER_APPEND_DISTRIB,iffRL TAKE_LENGTH_ID_rwt2]
  >> qmatch_goalsub_abbrev_tac `FILTER IS_SOME ll = _`
  >> `FILTER IS_SOME ll = []` by (
    qunabbrev_tac `ll`
    >> irule $ iffRL FILTER_EQ_NIL
    >> simp[EVERY_REPLICATE]
  )
  >> pop_assum $ fs o single
  >> qunabbrev_tac `ll`
  >> qmatch_goalsub_abbrev_tac `m < n`
  >> `n = m + 1` by (
    unabbrev_all_tac
    >> fs[offset_none_def,TAKE_APPEND1]
    >> fs[TAKE_APPEND,FILTER_APPEND_DISTRIB,iffRL TAKE_LENGTH_ID_rwt2]
    >> qmatch_goalsub_abbrev_tac `LENGTH _ + LENGTH l`
    >> `l = []` by fs[FILTER_EQ_NIL,Abbr`l`]
    >> fs[]
  )
  >> pop_assum $ fs o single
  >> map_every qunabbrev_tac [`m`,`n`]
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> qmatch_goalsub_abbrev_tac `offset_none (M ++ M')`
  >> `offset_none (M ++ M') t = LENGTH (FILTER IS_SOME M) + 1` by (
    qunabbrev_tac `M'`
    >> fs[offset_none_def,TAKE_APPEND1]
    >> fs[TAKE_APPEND,FILTER_APPEND_DISTRIB,iffRL TAKE_LENGTH_ID_rwt2]
    >> qmatch_goalsub_abbrev_tac `LENGTH _ + LENGTH l`
    >> `l = []` by fs[FILTER_EQ_NIL,Abbr`l`]
    >> fs[]
  )
  >> drule_then (qspec_then `M'` mp_tac) time_constraints_offset_none_APPEND_EQ
  >> fs[timeshift_def,bir_state_t_component_equality]
QED

Theorem cstep_seq_bisim:
  !p cid s M genv s' M' genv' r L.
  cstep_seq p cid (s, M, genv) (s', M', genv')
  /\ drop_none_rel s M r L
  ==> ?r' L'. cstep_seq p cid (r, L, genv) (r', L', genv')
    /\ drop_none_rel s' M' r' L'
Proof
  qsuff_tac `!p cid sMg sMg' r L.
    cstep_seq p cid sMg sMg'
    /\ drop_none_rel (FST sMg) (FST $ SND sMg) r L
    ==> ?r' L'. cstep_seq p cid (r, L, SND $ SND sMg) (r', L', SND $ SND sMg')
      /\ drop_none_rel (FST sMg') (FST $ SND sMg') r' L'`
  >- (rpt strip_tac >> first_x_assum drule >> fs[])
  >> fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac cstep_seq_ind
  >> rpt strip_tac
  >> simp[cstep_seq_cases]
  >> gvs[drop_none_rel_def]
  (* clstep *)
  >- (
    drule_all_then strip_assume_tac clstep_timeshift
    >> rpt $ goal_assum $ drule_at Any
  )
  (* cstep; clstep *)
  >> dsimp[]
  >> disj2_tac
  >> drule_all_then strip_assume_tac cstep_timeshift
  >> drule_all_then strip_assume_tac clstep_timeshift
  >> gs[FILTER_APPEND_DISTRIB]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem cstep_seq_rtc_bisim:
  !p cid s M genv s' M' genv' r L.
  cstep_seq_rtc p cid (s, M, genv) (s', M', genv')
  /\ drop_none_rel s M r L
  ==> ?r' L'. cstep_seq_rtc p cid (r, L, genv) (r', L', genv')
    /\ drop_none_rel s' M' r' L'
Proof
  qsuff_tac `!p cid sMg sMg' r L.
    cstep_seq_rtc p cid sMg sMg'
    /\ drop_none_rel (FST sMg) (FST $ SND sMg) r L
    ==> ?r' L'. cstep_seq_rtc p cid (r, L, SND $ SND sMg) (r', L', SND $ SND sMg')
      /\ drop_none_rel (FST sMg') (FST $ SND sMg') r' L'`
  >- (rpt strip_tac >> first_x_assum drule >> fs[])
  >> ntac 2 gen_tac
  >> fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,cstep_seq_rtc_def]
  >> ho_match_mp_tac RTC_INDUCT
  >> conj_tac
  >- fs[drop_none_rel_def]
  >> rw[]
  >> PairCases_on `sMg`
  >> PairCases_on `sMg'`
  >> PairCases_on `sMg''`
  >> fs[]
  >> drule_all_then strip_assume_tac cstep_seq_bisim
  >> first_x_assum $ drule_then strip_assume_tac
  >> irule_at Any $ cj 2 RTC_RULES
  >> rpt $ goal_assum $ drule_at Any
QED

Definition drop_none_rels_def:
  drop_none_rels cores M cores' M' <=>
    M' = FILTER IS_SOME M
    /\ (!cid p s. FLOOKUP cores cid = SOME $ Core cid p s
      ==> FLOOKUP cores' cid = SOME $ Core cid p $ timeshift (offset_none M) s
        /\ time_constraints (some_zero M) s)
    /\ (!cid p s. FLOOKUP cores' cid = SOME $ Core cid p s
      ==> ?s'. FLOOKUP cores cid = SOME $ Core cid p s' /\ s = timeshift (offset_none M) s')
End

Theorem parstep_seq_bisim:
  !cid cores M genv cores' M' genv' cores_some L.
    parstep cid cores M genv cores' M' genv'
    /\ drop_none_rels cores M cores_some L
  ==> ?cores_some' L'.
    parstep cid cores_some L genv cores_some' L' genv'
    /\ drop_none_rels cores' M' cores_some' L'
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac parstep_ind
  >> rpt strip_tac
  >> fs[parstep_cases,PULL_EXISTS,drop_none_rels_def]
  >> first_assum $ drule_then strip_assume_tac
  >> drule_all_then strip_assume_tac cstep_timeshift
  >> rpt $ goal_assum $ drule_at Any
  >> conj_tac
  (* atomicity_ok *)
  >- (
    fs[atomicity_ok_def,cores_pc_not_atomic_def,DOMSUB_FLOOKUP_THM,optionTheory.IS_SOME_EXISTS,PULL_EXISTS]
    >> rw[]
    >> PRED_ASSUM is_forall $ imp_res_tac
    >> last_x_assum $ drule_then drule
    >> gvs[timeshift_simps]
  )
  >> conj_tac
  (* is_certified *)
  >- (
    fs[is_certified_def]
    >> drule_then (qspecl_then [`timeshift (offset_none M') s'`,`FILTER IS_SOME M'`] mp_tac) cstep_seq_rtc_bisim
    >> impl_tac >- fs[drop_none_rel_def]
    >> disch_then strip_assume_tac
    >> goal_assum $ drule_at Any
    >> fs[drop_none_rel_def,timeshift_def]
  )
  >> rev_drule_then assume_tac cstep_mem_IS_PREFIX
  >> fs[IS_PREFIX_APPEND]
  >> qmatch_asmsub_rename_tac `M' = M ++ l`
  >> rw[FLOOKUP_UPDATE] >> fs[]
  >- (
    last_x_assum drule >> rw[]
    >> drule_then (qspec_then `l` assume_tac) time_constraints_offset_none_APPEND_EQ
    >> fs[]
  )
  >- (
    last_x_assum drule >> rw[time_constraints_APPEND]
  )
  >- (
    first_x_assum drule >> rw[]
    >> first_x_assum $ drule_then strip_assume_tac
    >> fs[time_constraints_offset_none_APPEND_EQ]
  )
QED

val _ = export_theory();
