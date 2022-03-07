open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "spinlock";

val (bir_spinlock_progbin_def, bir_spinlock_prog_def, bir_is_lifted_prog_spinlock) = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory tracesTheory;
open finite_mapTheory;

Theorem LT3 =
  (REWRITE_CONV [GSYM rich_listTheory.COUNT_LIST_COUNT,
    GSYM pred_setTheory.IN_COUNT]
    THENC EVAL) ``n < 3n``

Theorem LT5 =
  (REWRITE_CONV [GSYM rich_listTheory.COUNT_LIST_COUNT,
    GSYM pred_setTheory.IN_COUNT]
    THENC EVAL) ``n < 5n``

(*
 * characterisation of fulfil and promise rules
 *)

Definition is_fulfil_def:
  is_fulfil cid t sys1 sys2 =
  ?st st' p var e.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
    /\ bir_get_current_statement p st.bst_pc =
        SOME $ BStmtB $ BStmt_Assign var e
End

Theorem is_fulfil_MEM_bst_prom:
  !cid t sys1 sys2. is_fulfil cid t sys1 sys2
  ==> ?p st. FLOOKUP sys1 cid = SOME $ Core cid p st /\ MEM t st.bst_prom
Proof
  fs[is_fulfil_def,PULL_EXISTS]
QED

Definition is_promise_def:
  is_promise cid t sys1 sys2 =
  ?st st' p v l.
    FLOOKUP (FST sys1) cid = SOME $ Core cid p st
    /\ FLOOKUP (FST sys2) cid = SOME $ Core cid p st'
    /\ t = LENGTH (SND sys1) + 1
    /\ (SND sys2) = (SND sys1) ++ [<| loc := l; val := v; cid := cid  |>]
    /\ st'.bst_prom = st.bst_prom ++ [t]
End

(* fulfil steps change the state *)

Theorem is_fulfil_state_changed:
  !tr cid t p st st' i. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> st <> st'
Proof
  rpt strip_tac >> gvs[is_fulfil_def]
  >> qpat_x_assum `MEM _ _` mp_tac
  >> fs[]
  >> qpat_x_assum `FILTER _ _ = _` $ ONCE_REWRITE_TAC o single o GSYM
  >> fs[MEM_FILTER]
QED

(* promising steps change the state *)

Theorem is_promise_state_changed:
  !tr cid t p st st' i. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> st <> st'
Proof
  rpt strip_tac
  >> gvs[is_promise_def]
QED

(* parstep and fulfil transitions have same ids *)

Theorem is_fulfil_parstep_nice:
  !tr i cid cid' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid = cid'
Proof
  rpt strip_tac
  >> `parstep_nice cid (EL i tr) (EL (SUC i) tr)` by (
    CCONTR_TAC
    >> fs[is_fulfil_def]
    >> drule_at Any wf_trace_NOT_parstep_nice_state_EQ'
    >> rpt $ disch_then drule
    >> disch_then $ fs o single
    >> drule_at Any FILTER_NEQ_NOT_MEM
    >> fs[EQ_SYM_EQ]
  )
  >> dxrule_at_then Any (drule_at Any) parstep_nice_parstep_nice
  >> fs[]
QED

Theorem is_fulfil_parstep_nice_imp:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all is_fulfil_parstep_nice
  >> fs[]
QED

Theorem is_fulfil_memory:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> SND $ EL i tr = SND $ EL (SUC i) tr
Proof
  rpt strip_tac
  >> imp_res_tac is_fulfil_parstep_nice_imp
  >> gvs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE,is_fulfil_def]
  >> `MEM t $ FILTER ($<> t) s.bst_prom` by fs[EQ_SYM_EQ]
  >> fs[MEM_FILTER]
QED

Theorem is_fulfil_parstep_nice_eq:
  !tr cid t i. wf_trace tr /\ SUC i < LENGTH tr
    /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
    ==>  ?p s var xcl e v_e v_data v_addr v l new_viewenv new_env a_e.
    bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl
    /\ xcl = is_xcl_write p s.bst_pc
    /\  MEM t s.bst_prom
    /\  is_certified p cid
          (s with
           <|bst_pc :=
               if xcl then
                 bir_pc_next (bir_pc_next (bir_pc_next s.bst_pc))
               else bir_pc_next s.bst_pc; bst_environ := new_env;
             bst_viewenv := new_viewenv;
             bst_coh :=
               (λlo. if lo = l then MAX (s.bst_coh l) t else s.bst_coh lo);
             bst_v_wOld := MAX s.bst_v_wOld t;
             bst_v_CAP := MAX s.bst_v_CAP v_addr;
             bst_prom updated_by FILTER (λt'. t' ≠ t);
             bst_fwdb :=
               (λlo.
                    if lo = l then
                      <|fwdb_time := t; fwdb_view := MAX v_addr v_data;
                        fwdb_xcl := xcl |>
                    else s.bst_fwdb lo);
             bst_xclb := if xcl then NONE else s.bst_xclb|>)
          (SND (EL (SUC i) tr))
    /\  SOME new_viewenv =
        fulfil_update_viewenv p s xcl t
    /\  SOME new_env = fulfil_update_env p s xcl
    /\  s.bst_coh l < t
    /\  (if xcl then get_xclb_view s.bst_xclb else 0) < t
    /\  s.bst_v_CAP < t
    /\  s.bst_v_wNew < t
    /\  v_data < t
    /\  v_addr < t
    /\  t < LENGTH (SND (EL (SUC i) tr)) + 1
    /\  EL (PRE t) (SND (EL (SUC i) tr)) = <|loc := l; val := v; cid := cid|>
    /\  (xcl ==> fulfil_atomic_ok (SND (EL (SUC i) tr)) l cid s t)
    /\  (SOME v,v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    /\  (SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\  get_fulfil_args e = SOME (a_e,v_e)
    /\  bir_get_current_statement p s.bst_pc =
        SOME (BStmtB (BStmt_Assign var e))
    /\  atomicity_ok cid (FST (EL i tr))
    /\  FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
    /\  FST (EL (SUC i) tr) =
        FST (EL i tr) |+
        (cid,
         Core cid p
           (s with
            <|bst_pc :=
                if xcl then
                  bir_pc_next (bir_pc_next (bir_pc_next s.bst_pc))
                else bir_pc_next s.bst_pc; bst_environ := new_env;
              bst_viewenv := new_viewenv;
              bst_coh :=
                (λlo. if lo = l then MAX (s.bst_coh l) t else s.bst_coh lo);
              bst_v_wOld := MAX s.bst_v_wOld t;
              bst_v_CAP := MAX s.bst_v_CAP v_addr;
              bst_prom updated_by FILTER (λt'. t' ≠ t);
              bst_fwdb :=
                (λlo.
                     if lo = l then
                       <|fwdb_time := t; fwdb_view := MAX v_addr v_data;
                         fwdb_xcl := xcl |>
                     else s.bst_fwdb lo);
              bst_xclb :=
                if xcl then NONE else s.bst_xclb|>))
    /\  SND (EL i tr) = SND (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then assume_tac is_fulfil_parstep_nice_imp
  >> drule_all_then assume_tac is_fulfil_memory
  >> gvs[parstep_nice_def,parstep_cases,clstep_cases,cstep_cases,is_fulfil_def,FLOOKUP_UPDATE,bir_programTheory.bir_state_t_accfupds,stmt_generic_step_def,bir_get_stmt_branch,bir_get_stmt_generic,FILTER_EQ_ID,EVERY_MEM,bir_get_stmt_write]
  >> dxrule_at_then Any (drule_at Any) FILTER_NEQ_MEM_EQ
  >> impl_tac
  >- (
    CONV_TAC $ RATOR_CONV $ ONCE_DEPTH_CONV SYM_CONV
    >> CONV_TAC $ RAND_CONV $ ONCE_DEPTH_CONV SYM_CONV
    >> fs[]
  )
  >> disch_then $ fs o single
  >> rpt $ goal_assum $ drule_at Any
  >> fs[]
QED

(* parstep and promise transitions have same ids *)

Theorem is_promise_parstep_nice:
  !tr i cid cid' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid = cid'
Proof
  rpt strip_tac
  >> fs[parstep_nice_def,parstep_cases,cstep_cases,clstep_cases,is_promise_def]
  >> gvs[]
QED

Theorem is_promise_parstep_nice_imp:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  ==> parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all is_promise_parstep_nice
  >> fs[]
QED

Theorem is_promise_parstep_nice_eq:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  ==> ?msg p s. cid = msg.cid
    /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
    /\  SND (EL (SUC i) tr) = SND (EL i tr) ⧺ [msg]
    /\  FST (EL (SUC i) tr) =
        FST (EL i tr) |+
        (cid,
          Core cid p
            (s with
            bst_prom updated_by (λpr. pr ⧺ [LENGTH (SND (EL i tr)) + 1])))
    /\  atomicity_ok cid (FST (EL i tr))
    /\  is_certified p cid
          (s with
            bst_prom updated_by (λpr. pr ⧺ [LENGTH (SND (EL i tr)) + 1]))
          (SND (EL i tr) ⧺ [msg])
Proof
  rpt strip_tac
  >> imp_res_tac is_promise_parstep_nice_imp
  >> fs[parstep_nice_def,parstep_cases,cstep_cases,clstep_cases,is_promise_def]
  >> gvs[]
QED

(* fulfil steps affect only the fulfiling core *)

Theorem is_fulfil_inv:
  !tr cid cid' t p p2 p2' st st' st2 st2' i.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ FLOOKUP (FST $ EL i tr) cid' = SOME $ Core cid' p2 st2
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid' = SOME $ Core cid' p2' st2'
  /\ cid <> cid'
  ==> st <> st' /\ p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    drule_then irule is_fulfil_state_changed
    >> rpt $ goal_assum $ drule_at Any
  )
  >>  drule_then (drule_then irule) wf_trace_unchanged
  >> rpt $ goal_assum $ drule_at Any
QED

(* promise steps affect only the promising core *)

Theorem is_promise_inv:
  !tr cid cid' t p p2 p2' st st' st2 st2' i.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ FLOOKUP (FST $ EL i tr) cid' = SOME $ Core cid' p2 st2
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid' = SOME $ Core cid' p2' st2'
  /\ cid <> cid'
  ==> st <> st' /\ p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    drule_then irule is_promise_state_changed
    >> rpt $ goal_assum $ drule_at Any
  )
  >>  drule_then (drule_then irule) wf_trace_unchanged
  >> rpt $ goal_assum $ drule_at Any
QED

(* a promise entails lower bound of future memory length *)

Theorem is_promise_LENGTH_SND_EL:
  !i j tr cid t. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ SUC i <= j /\ j < LENGTH tr
  ==> t <= LENGTH (SND $ EL j tr)
Proof
  rpt gen_tac
  >> Induct_on `j - SUC i`
  >- (rw[is_promise_def] >> gs[LESS_OR_EQ])
  >> rw[SUB_LEFT_EQ]
  >> first_x_assum $ rev_drule_at Any
  >> disch_then $ rev_drule_at Any
  >> disch_then $ qspec_then `v + SUC i` assume_tac
  >> `SUC $ v + SUC i < LENGTH tr` by fs[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> dxrule_then strip_assume_tac parstep_nice_memory_imp
  >> gs[]
  >> `SUC i + SUC v = SUC $ v + SUC i` by fs[]
  >> pop_assum $ fs o single
QED

(* a promise is only promised once *)

Theorem is_promise_once:
  !i j tr cid cid' t. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ i < j /\ SUC j < LENGTH tr
  ==> ~is_promise cid' t (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> rev_drule_at Any is_promise_LENGTH_SND_EL
  >> disch_then $ rev_drule_at_then Any assume_tac
  >> first_assum $ qspec_then `j` assume_tac
  >> first_x_assum $ qspec_then `SUC j` assume_tac
  >> dxrule_then strip_assume_tac $ iffLR is_promise_def
  >> gvs[]
QED

(* a fulfil has an earlier promise *)

Theorem NOT_is_promise_NOT_MEM_bst_prom:
  !i tr cid p st st' t. wf_trace tr
  /\ ~is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ ~MEM t st.bst_prom
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> ~MEM t st'.bst_prom
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> Cases_on `cid = cid'`
  >- (
    BasicProvers.VAR_EQ_TAC
    >> fs[is_promise_def,DISJ_EQ_IMP]
    >> fs[AND_IMP_INTRO,AC CONJ_ASSOC CONJ_COMM,cstep_cases,parstep_nice_def,parstep_cases]
    (* execute *)
    >- (
      imp_res_tac clstep_LENGTH_prom
      >> gvs[FLOOKUP_UPDATE]
      >- (imp_res_tac clstep_bst_prom_EQ >> fs[])
      >> gvs[clstep_cases,MEM_FILTER,FLOOKUP_UPDATE]
    )
    (* promises *)
    >> spose_not_then assume_tac
    >> gvs[FLOOKUP_UPDATE,mem_msg_t_component_equality]
  )
  >> gs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
QED

Theorem is_fulfil_is_promise:
  !i tr cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> ?j. j < i /\ is_promise cid t (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[DISJ_EQ_IMP]
  >> `!j p st. j <= i /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
    ==> ~MEM t st.bst_prom` by (
    Induct
    >- (
      rw[] >> fs[wf_trace_def,empty_prom_def]
      >> strip_tac
      >> res_tac
      >> gs[NULL_EQ]
    )
    >> rw[] >> gs[]
    >> `j < i` by fs[]
    >> first_x_assum $ dxrule_then assume_tac
    >> drule_then drule wf_trace_cid_backward1
    >> rw[]
    >> first_x_assum $ drule_then assume_tac
    >> drule_then drule NOT_is_promise_NOT_MEM_bst_prom
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >> fs[is_fulfil_def]
  >> first_x_assum $ rev_drule_at Any
  >> fs[]
QED

(* a promise has a succeeding fulfil *)

Theorem NOT_is_fulfil_MEM_bst_prom:
  !i tr cid p st p' st' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ ~is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ MEM t st.bst_prom
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> MEM t st'.bst_prom
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,parstep_cases,is_fulfil_def,DISJ_EQ_IMP]
  >> Cases_on `cid = cid'`
  >> gvs[FLOOKUP_UPDATE,is_promise_def,DISJ_EQ_IMP]
  >> fs[AND_IMP_INTRO,AC CONJ_ASSOC CONJ_COMM,cstep_cases,parstep_nice_def,parstep_cases]
  >> imp_res_tac clstep_LENGTH_prom
  >> gvs[FLOOKUP_UPDATE]
  >- (imp_res_tac clstep_bst_prom_EQ >> fs[])
  >> gvs[clstep_cases,MEM_FILTER,FLOOKUP_UPDATE]
  >> spose_not_then assume_tac
  >> gvs[]
  >> imp_res_tac $ iffLR bir_get_stmt_write
  >> imp_res_tac $ iffLR bir_get_stmt_read
  >> fs[]
QED

Theorem is_promise_is_fulfil:
  !i tr cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  ==> ?j. i < j /\ SUC j < LENGTH tr
    /\ is_fulfil cid t (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[DISJ_EQ_IMP]
  >> `!j p st. i <= j /\ SUC j < LENGTH tr
    /\ FLOOKUP (FST $ EL (SUC j) tr) cid = SOME $ Core cid p st
    ==> MEM t st.bst_prom` by (
    Induct_on `j - i`
    >- (
      rw[] >> gvs[LESS_OR_EQ,is_promise_def,FLOOKUP_UPDATE]
    )
    >> rw[SUB_LEFT_EQ] >> fs[]
    >> first_x_assum $ qspecl_then [`i + v`,`i`] mp_tac
    >> fs[]
    >> `?st. FLOOKUP (FST $ EL (SUC $ i + v) tr) cid = SOME $ Core cid p st` by (
      irule wf_trace_cid_backward1
      >> `SUC $ i + SUC v = SUC $ SUC $ i + v` by fs[]
      >> pop_assum $ fs o single
    )
    >> disch_then $ drule_then assume_tac
    >> drule NOT_is_fulfil_MEM_bst_prom
    >> rpt $ disch_then $ drule_at Any
    >> disch_then irule
    >> fs[]
    >> `SUC $ i + SUC v = SUC $ SUC $ i + v` by fs[]
    >> pop_assum $ fs o single
  )
  >> `?p st. FLOOKUP (FST $ LAST tr) cid = SOME $ Core cid p st` by (
    fs[is_promise_def,GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL]
    >> qexists_tac `p`
    >> drule_then irule wf_trace_cid_forward
    >> fs[]
    >> goal_assum $ drule_at Any
    >> fs[]
  )
  >> drule_all wf_trace_LAST_NULL_bst_prom
  >> gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL]
  >> Cases_on `SUC i = PRE $ LENGTH tr`
  >- fs[is_promise_def]
  >> gs[NOT_NUM_EQ]
  >> `i <= PRE $ PRE $ LENGTH tr` by fs[]
  >> first_x_assum dxrule
  >> `0 < PRE $ LENGTH tr` by fs[]
  >> fs[iffLR SUC_PRE]
  >> rw[LENGTH_NOT_NULL,MEM_SPLIT,NOT_NULL_MEM]
  >> goal_assum drule
QED

(* every addition to memory is a promise *)

Theorem wf_trace_EL_SND_is_promise:
  !i tr k. wf_trace tr /\ i < LENGTH tr
  /\ k < LENGTH $ SND $ EL i tr
  ==> ?j. j < i
    /\ is_promise (EL k $ SND $ EL i tr).cid (SUC k) (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `is_promise cid _ _`
  >> drule wf_trace_adds_to_memory
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then `cid` assume_tac
  >> fs[Abbr`cid`]
  >> goal_assum drule
  >> gs[is_promise_def,FLOOKUP_UPDATE,parstep_nice_def,parstep_cases,cstep_cases,mem_msg_t_component_equality]
QED

(* the timestamp of a fulfil is coupled to the fulfiled core *)

Theorem is_fulfil_to_memory:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> 0 < t /\ t < (LENGTH $ SND $ EL i tr) + 1
    /\ (EL (PRE t) $ SND $ EL i tr).cid = cid
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then strip_assume_tac is_fulfil_parstep_nice_eq
  >> fs[]
QED

(* a fulfil is only fulfilled once *)

Theorem is_fulfil_once:
  !tr i j t cid cid'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC j < LENGTH tr /\ i <> j
  ==> ~is_fulfil cid' t (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> wlog_tac `i < j` [`i`,`j`,`cid`,`cid'`]
  >- metis_tac[NOT_NUM_EQ,LESS_EQ]
  >> qmatch_assum_rename_tac `is_fulfil cid t (FST $ EL i tr) _`
  >> qmatch_assum_rename_tac `is_fulfil cid' t (FST $ EL j tr) _`
  >> drule_at (Pos $ el 3) is_fulfil_to_memory
  >> rev_drule_at (Pos $ el 3) is_fulfil_to_memory
  >> drule_at (Pos $ el 3) is_fulfil_memory
  >> rev_drule_at (Pos $ el 3) is_fulfil_memory
  >> rpt strip_tac >> gs[]
  >> `cid = cid'` by (
    drule_then (qspecl_then [`SUC i`,`SUC j`] mp_tac) wf_trace_IS_PREFIX_SND_EL
    >> rw[IS_PREFIX_APPEND]
    >> fs[EL_APPEND1]
  )
  >> ntac 2 $ qpat_x_assum `_.cid = _` kall_tac
  >> gvs[]
  >> Cases_on `j = SUC i`
  >> gvs[FLOOKUP_UPDATE,is_fulfil_def]
  >> drule_then (rev_drule_then $ drule_at Any) wf_trace_cid
  >> disch_then strip_assume_tac
  >> gvs[]
  >- (
    ntac 2 $ qhdtm_x_assum `FILTER` $ fs o single o GSYM
    >> fs[MEM_FILTER]
  )
  >> qspecl_then [`SUC i`,`j`,`tr`,`cid`] assume_tac
    wf_trace_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom
  >> gs[EVERY_MEM,AND_IMP_INTRO]
  >> first_x_assum drule
  >> impl_tac
  >- (
    ntac 2 $ qhdtm_x_assum `FILTER` $ fs o single o GSYM
    >> fs[MEM_FILTER]
  )
  >> fs[NOT_LESS]
QED

(* only one fulfil happens at a time *)

Theorem is_fulfil_same:
  !tr cid cid' t t' i. wf_trace tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil cid' t' (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> cid = cid' /\ t = t'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    ntac 2 $ drule_then (drule_then $ dxrule_then assume_tac) is_fulfil_parstep_nice_imp
    >> dxrule_at_then Any irule parstep_nice_parstep_nice
    >> fs[]
  )
  >> gvs[is_fulfil_def]
  >> qhdtm_x_assum `FILTER` $ fs o single o GSYM
  >> dxrule_at_then Any (dxrule_at Any) FILTER_NEQ_MEM_EQ
  >> fs[EQ_SYM_EQ]
QED

(* only one promise happens at a time *)

Theorem is_promise_same:
  !tr cid cid' t t' i. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ is_promise cid' t' (EL i tr) (EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> cid = cid' /\ t = t'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    ntac 2 $ drule_then (drule_then $ dxrule_then assume_tac) is_promise_parstep_nice_imp
    >> dxrule_at_then Any irule parstep_nice_parstep_nice
    >> fs[]
  )
  >> fs[is_promise_def]
QED

(* For a thread cid, the coh(l) of an address l fulfiled to is strictly larger than t *)
Theorem is_fulfil_bst_coh:
  !tr i j cid t p st. wf_trace tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ i < j /\ j < LENGTH tr
  /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
  ==> t < st.bst_coh((EL t $ SND $ EL (SUC i) tr).loc)
Proof
  rpt gen_tac
  >> Induct_on `j - i` >> fs[]
  >> rw[SUB_LEFT_EQ]
  >> first_x_assum $ qspecl_then [`v + i`,`i`] assume_tac
  >> Cases_on `0 < v`
  >> gs[]
  >- (
    cheat
  )
  >> drule_at_then (Pos $ el 3) assume_tac is_fulfil_parstep_nice_imp
  >> drule_at_then (Pos $ el 3) assume_tac is_fulfil_to_memory
  >> gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
  >> cheat
QED

(*
 * exclusive store and read pairs
 *)

Definition is_read_xcl_def:
  is_read_xcl cid t sys1 sys2 <=>
  ?st st' p var a_e cast_opt.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ bir_get_stmt p st.bst_pc = BirStmt_Read var a_e cast_opt T
    /\ IS_SOME st'.bst_xclb
    /\ (THE st'.bst_xclb).xclb_time = t
    /\ IS_NONE st.bst_xclb
End

Definition is_fulfil_xcl_def:
  is_fulfil_xcl cid t sys1 sys2 <=>
  ?st st' p a_e v_e.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
    /\ bir_get_stmt p st.bst_pc = BirStmt_Write a_e v_e T
    /\ IS_SOME st.bst_xclb
End

Theorem is_fulfil_xcl_is_fulfil:
  !cid t sys1 sys2. is_fulfil_xcl cid t sys1 sys2 ==> is_fulfil cid t sys1 sys2
Proof
  rw[is_fulfil_xcl_def,is_fulfil_def,bir_get_stmt_write]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem is_fulfil_xcl_atomic:
  !tr i cid t p st.  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> fulfil_atomic_ok (SND $ EL i tr) ((EL (PRE t) $ SND $ EL i tr).loc) cid st t
    /\ is_xcl_write p st.bst_pc
Proof
  rpt gen_tac >> strip_tac
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> drule_at_then Any assume_tac is_fulfil_parstep_nice_eq
  >> gs[is_fulfil_xcl_def,bir_get_stmt_write]
QED

(* parstep and read transitions have same ids *)

Theorem is_read_xcl_parstep_nice:
  !tr i cid cid' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid = cid'
Proof
  rpt strip_tac
  >> `parstep_nice cid (EL i tr) (EL (SUC i) tr)` by (
    CCONTR_TAC
    >> fs[is_read_xcl_def]
    >> drule_at Any wf_trace_NOT_parstep_nice_state_EQ'
    >> rpt $ disch_then drule
    >> disch_then $ fs o single
  )
  >> dxrule_at_then Any (drule_at Any) parstep_nice_parstep_nice
  >> fs[]
QED

Theorem is_read_xcl_parstep_nice_imp:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all is_read_xcl_parstep_nice
  >> fs[]
QED

(* parstep transition of an exclusive read *)

Theorem is_read_xcl_parstep_nice_eq:
  !tr cid t i. wf_trace tr /\ SUC i < LENGTH tr
    /\ is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
    ==> ?p s st' opt_cast ν_pre v_addr new_env l a_e var v.
    is_certified p cid st' (SND (EL (SUC i) tr))
    /\ st' = (s with
           <|bst_pc := bir_pc_next (bir_pc_next s.bst_pc);
             bst_environ := new_env;
             bst_viewenv updated_by
               (λenv.
                    env |+
                    (var,
                     MAX (MAX v_addr s.bst_v_rNew)
                       (mem_read_view (s.bst_fwdb l) t)));
             bst_coh :=
               (λlo.
                    if lo = l then
                      MAX (s.bst_coh l)
                        (MAX (MAX v_addr s.bst_v_rNew)
                           (mem_read_view (s.bst_fwdb l) t))
                    else s.bst_coh lo);
             bst_v_rOld :=
               MAX s.bst_v_rOld
                 (MAX (MAX v_addr s.bst_v_rNew)
                    (mem_read_view (s.bst_fwdb l) t));
             bst_v_CAP := MAX s.bst_v_CAP v_addr;
             bst_xclb :=
               SOME
                 <|xclb_time := t;
                   xclb_view :=
                     MAX (MAX v_addr s.bst_v_rNew)
                       (mem_read_view (s.bst_fwdb l) t)|> |>)
    /\  SOME new_env =
        env_update_cast64 (bir_var_name var) v (bir_var_type var) s.bst_environ
    /\  (∀t'.
          t < t' ∧ (t' ≤ ν_pre ∨ t' ≤ s.bst_coh l) ⇒
          (EL t' (SND (EL i tr))).loc ≠ l)
    /\  mem_read (SND (EL i tr)) l t = SOME v
    /\  (SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\  bir_get_stmt p s.bst_pc = BirStmt_Read var a_e opt_cast T
    /\  SND (EL (SUC i) tr) = SND (EL i tr)
    /\  atomicity_ok cid (FST (EL i tr))
    /\  FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
    /\  FST (EL (SUC i) tr) = FST (EL i tr) |+ (cid, Core cid p st')
Proof
  rpt strip_tac
  >> imp_res_tac is_read_xcl_parstep_nice_imp
  >> dxrule_then assume_tac $ iffLR parstep_nice_def
  >> dxrule_then strip_assume_tac $ iffLR parstep_cases
  >> rpt $ goal_assum $ drule_at Any
  >> gvs[cstep_cases,clstep_cases,is_read_xcl_def,optionTheory.IS_SOME_EXISTS,is_read_xcl_def,FLOOKUP_UPDATE]
  >> rpt $ goal_assum $ drule_at Any
  >> dsimp[bir_programTheory.bir_state_t_component_equality,pairTheory.ELIM_UNCURRY,FUN_EQ_THM,mem_read_view_def]
QED

(* only exclusive loads set the exclusive bank *)

Theorem xclb_NONE_SOME_is_read_xclb:
  !cid p p' st st' i tr. wf_trace tr /\ SUC i < LENGTH tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ IS_SOME st'.bst_xclb
  /\ st.bst_xclb = NONE
  ==> ?t. is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,parstep_cases,DISJ_EQ_IMP]
  >> Cases_on `cid = cid'`
  >> gvs[FLOOKUP_UPDATE,clstep_cases,cstep_cases,parstep_nice_def,parstep_cases,is_read_xcl_def,optionTheory.IS_SOME_EXISTS]
  >- (
    gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_get_stmt_branch,AllCaseEqs()]
  )
  >> qmatch_assum_rename_tac `bir_exec_stmt p stmt s = _`
  >> Cases_on `stmt`
  >- (
    qmatch_assum_rename_tac `bir_exec_stmt p (BStmtB b) s = _`
    >> Cases_on `b`
    >> fs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def,bir_programTheory.bir_state_is_terminated_def,bir_programTheory.bir_exec_stmtB_def,bir_get_stmt_generic]
    >> BasicProvers.every_case_tac
    >> fs[Once EQ_SYM_EQ]
    >> cheat
  )
  >> cheat
QED

(* a successful exclusive store has an earlier exclusive load *)
(* TODO encode success *)
Theorem is_fulfil_xcl_is_read_xcl:
  !i tr cid p st t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> ?j. j < i
    /\ is_read_xcl cid t (FST $ EL j tr) (FST $ EL (SUC j) tr)
    /\ !k p' st'. j < k /\ k <= i
      /\ FLOOKUP (FST $ EL k tr) cid = SOME $ Core cid p st'
      ==> st.bst_xclb = st'.bst_xclb
Proof
  rpt strip_tac
  >> drule_then assume_tac is_fulfil_xcl_is_fulfil
  >> drule_all_then strip_assume_tac is_fulfil_is_promise
  (* TODO there is a (last) process that sets the exclusive bank *)
  >> qabbrev_tac `P = λj. 1 < j /\ LENGTH tr - j < i /\ j <= LENGTH tr
    /\ !st st'. FLOOKUP (FST $ EL (LENGTH tr - j) tr) cid = SOME $ Core cid p st
      /\ FLOOKUP (FST $ EL (SUC $ LENGTH tr - j) tr) cid = SOME $ Core cid p st'
      ==> IS_NONE st.bst_xclb /\ IS_SOME st'.bst_xclb`
  >> Cases_on `?i. P i`
  >- (
    dxrule_then assume_tac arithmeticTheory.WOP
    >> fs[Abbr`P`,DISJ_EQ_IMP,AND_IMP_INTRO]
    >> drule_then (drule_then $ qspec_then `LENGTH tr - n` assume_tac) wf_trace_cid
    >> gs[]
    >> cheat
    >> `is_read_xcl cid t (FST (EL (LENGTH tr - n) tr)) (FST (EL (SUC $ LENGTH tr - n) tr))` by (
      irule xclb_NONE_SOME_is_read_xclb
      >> fs[]
    )
    >> goal_assum $ drule_at Any
    (* TODO by xclb_NONE_SOME_is_read_xclb, this is an exclusive load *)
    >> cheat
  )
  >> cheat
QED

(*
 * correctness of spinlock
 *)

Theorem varset_of_spinlock_prog =
  EVAL ``bir_varset_of_program $ bir_spinlock_prog:string bir_program_t``

Definition spinlock_var_def:
  spinlock_var = BVar "x7" $ BType_Imm Bit64
End

Theorem spinlock_var_in_varset_of_spinlock_prog:
  spinlock_var IN bir_varset_of_program $ bir_spinlock_prog:string bir_program_t
Proof
  fs[varset_of_spinlock_prog,spinlock_var_def]
QED

Definition core_runs_prog_def:
  core_runs_prog cid s prog =
    ?st. FLOOKUP s cid = SOME $ Core cid prog st
    /\ st = <|
      bst_pc      := bir_program$bir_pc_first prog
    ; bst_environ  := bir_env_default $ bir_envty_of_vs $
                        bir_varset_of_program prog
    ; bst_status := BST_Running
    ; bst_viewenv := FEMPTY
    ; bst_coh := \x.0
    ; bst_v_rOld := 0
    ; bst_v_CAP := 0
    ; bst_v_rNew := 0
    ; bst_v_wNew := 0
    ; bst_v_wOld := 0
    ; bst_prom := []
    ; bst_inflight := []
    ; bst_fwdb := (\l. <| fwdb_time:= 0; fwdb_view:=0; fwdb_xcl:=F |>)
    ; bst_counter := 0
    ; bst_xclb := NONE
  |>
End

Definition core_runs_spinlock_def:
  core_runs_spinlock cid s =
    core_runs_prog cid s (bir_spinlock_prog:string bir_program_t)
End

Definition cores_run_spinlock_def:
  cores_run_spinlock s =
    !cid p st. FLOOKUP s cid = SOME $ Core cid p st
      ==> core_runs_spinlock cid s
End

(* the core runs the spinlock program at any time *)

Theorem wf_trace_core_runs_spinlock_FLOOKUP:
  !tr i cid p s. wf_trace tr
  /\ i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
  ==> p = (bir_spinlock_prog:string bir_program_t)
Proof
  rpt strip_tac
  >> drule_at_then Any (qspec_then `0` assume_tac) wf_trace_cid_backward
  >> gs[core_runs_spinlock_def,core_runs_prog_def]
QED

Theorem wf_trace_core_runs_spinlock_FLOOKUP':
  !tr i cid p s. wf_trace tr
  /\ i < LENGTH tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
  /\ cores_run_spinlock $ FST $ HD tr
  ==> core_runs_spinlock cid $ FST $ HD tr
Proof
  rw[cores_run_spinlock_def]
  >> drule_then drule wf_trace_cid_backward
  >> disch_then $ qspec_then `0` assume_tac
  >> gs[]
QED

(* the labels of the spinlock program *)

Theorem bir_spinlock_prog_labels:
  !l. IS_SOME $ bir_get_program_block_info_by_label (bir_spinlock_prog:'a bir_program_t) l
  <=> ?c. l = BL_Address $ Imm64 c /\ c IN {0w; 4w; 8w; 12w; 16w; 20w; 24w}
Proof
  EVAL_TAC
  >> dsimp[]
  >> rw[]
QED

Theorem bir_get_stmt_bir_spinlock_prog:
  !x y. bir_get_stmt (bir_spinlock_prog:'a bir_program_t) x = y /\ y <> BirStmt_None
  ==> ?c. x.bpc_label = BL_Address $ Imm64 c /\ c IN {0w; 4w; 8w; 12w; 16w; 20w; 24w}
Proof
  rw[GSYM bir_spinlock_prog_labels,bir_get_stmt_def]
  >> gs[bir_programTheory.bir_get_current_statement_def,CaseEq"option",quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
QED

Theorem bir_get_program_block_info_by_label' =
  LIST_CONJ $ List.map
    (fn x => EVAL ``bir_get_program_block_info_by_label bir_spinlock_prog $ BL_Address $ Imm64 ^(Term x)``)
    [`0w:word64`, `4w:word64`, `8w:word64`, `12w:word64`, `16w:word64`, `20w:word64`, `24w:word64`]

Theorem bir_labels_of_program_bir_spinlock_prog =
  EVAL ``bir_labels_of_program (bir_spinlock_prog:'a bir_program_t)``

(* all reads in the spinlock program *)

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ:
  !pc var a_e opt_cast xcl.
  bir_get_stmt (bir_spinlock_prog:string bir_program_t) pc
  = BirStmt_Read var a_e opt_cast xcl
  <=> pc = <| bpc_index := 1; bpc_label := BL_Address $ Imm64 12w|>
    /\ var = BVar "x5" $ BType_Imm Bit64
    /\ opt_cast = SOME (BIExp_SignedCast,Bit64)
    /\ a_e = BExp_Den spinlock_var
    /\ xcl
Proof
  fs[EQ_IMP_THM]
  >> rpt gen_tac >> ntac 2 strip_tac
  >- (
    fs[bir_get_stmt_read,bir_programTheory.bir_get_current_statement_def,CaseEq"option",pairTheory.ELIM_UNCURRY,spinlock_var_def]
    >> BasicProvers.every_case_tac
    >> fs[]
    >> imp_res_tac $ REWRITE_RULE[optionTheory.IS_SOME_EXISTS] $ iffLR bir_spinlock_prog_labels
    >> gs[bir_get_program_block_info_by_label',bir_programTheory.bir_pc_next_def]
    >> gs[bir_programTheory.bir_programcounter_t_component_equality,LT5,LT3,get_read_args_def,bir_auxiliaryTheory.NUM_LSONE_EQZ]
    >> gs[is_xcl_read_thm,bir_programTheory.bir_pc_next_def,bir_programTheory.bir_programcounter_t_literal_11,bir_programTheory.bir_programcounter_t_accfupds,bir_programTheory.bir_get_current_statement_def,CaseEq"option",bir_get_program_block_info_by_label']
  )
  >> fs[bir_get_stmt_read,bir_programTheory.bir_get_current_statement_def,CaseEq"option",pairTheory.ELIM_UNCURRY,spinlock_var_def,PULL_EXISTS,bir_get_program_block_info_by_label',get_read_args_def,is_xcl_read_thm,bir_programTheory.bir_pc_next_def]
QED

(* all writes in the spinlock program *)

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ:
  !pc a_e v_e xcl.
  bir_get_stmt (bir_spinlock_prog:string bir_program_t) pc
  = BirStmt_Write a_e v_e xcl
  <=> (
    pc = <| bpc_index := 2; bpc_label := BL_Address $ Imm64 12w|>
    /\ a_e = BExp_Den spinlock_var
    /\ v_e = BExp_Const (Imm32 0x1010101w)
    /\ ~xcl
  ) \/ (
    pc = <| bpc_index := 2; bpc_label := BL_Address $ Imm64 20w|>
    /\ a_e = BExp_Den spinlock_var
    /\ v_e = BExp_Cast BIExp_LowCast (BExp_Den $ BVar "x0" $ BType_Imm Bit64) Bit32
    /\ xcl
  )
Proof
  fs[EQ_IMP_THM]
  >> rpt gen_tac >> ntac 2 strip_tac
  >- (
    fs[bir_get_stmt_write,bir_programTheory.bir_get_current_statement_def,CaseEq"option",pairTheory.ELIM_UNCURRY,spinlock_var_def]
    >> BasicProvers.every_case_tac
    >> fs[]
    >> imp_res_tac $ REWRITE_RULE[optionTheory.IS_SOME_EXISTS] $ iffLR bir_spinlock_prog_labels
    >> gs[bir_get_program_block_info_by_label',bir_programTheory.bir_pc_next_def]
    >> gs[bir_programTheory.bir_programcounter_t_component_equality,LT5,LT3,get_fulfil_args_def,bir_auxiliaryTheory.NUM_LSONE_EQZ]
    >> gs[is_xcl_write_thm,bir_programTheory.bir_pc_next_def,bir_programTheory.bir_programcounter_t_literal_11,bir_programTheory.bir_programcounter_t_accfupds,bir_programTheory.bir_get_current_statement_def,CaseEq"option",bir_get_program_block_info_by_label']
  )
  >> fs[bir_get_stmt_write,bir_programTheory.bir_get_current_statement_def,CaseEq"option",pairTheory.ELIM_UNCURRY,spinlock_var_def,PULL_EXISTS,bir_get_program_block_info_by_label',get_fulfil_args_def,is_xcl_write_thm,bir_programTheory.bir_pc_next_def]
QED

(* an exclusive fulfil writes to the spinlock_var *)

Theorem core_runs_spinlock_is_fulfil_xcl_memory_location:
  !tr i cid t p st. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> bir_eval_exp (BExp_Den spinlock_var) st.bst_environ
    = SOME $ (EL (PRE t) $ SND $ EL i tr).loc
    /\ ?v. (EL (PRE t) $ SND $ EL i tr).val = BVal_Imm v
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then assume_tac is_fulfil_xcl_is_fulfil
  >> dxrule_at_then (Pat `is_fulfil _ _ _`) assume_tac is_fulfil_parstep_nice_eq
  >> drule_at Any wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ drule_at_then Any assume_tac
  >> gvs[is_fulfil_xcl_def,FLOOKUP_UPDATE,bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ]
  >> qhdtm_x_assum `is_certified` kall_tac
  >> qpat_x_assum `FST _ = _` kall_tac
  >> fs[bir_expTheory.bir_eval_exp_def,bir_eval_exp_view_def,bir_envTheory.bir_env_read_def]
  >> BasicProvers.every_case_tac
  >> fs[bir_expTheory.bir_eval_cast_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_name_def]
  >> qmatch_asmsub_rename_tac `bir_env_lookup "x0" st.bst_environ`
  >> Cases_on `bir_env_lookup "x0" st.bst_environ`
  >> gs[bir_expTheory.bir_eval_cast_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_name_def]
  >> qmatch_asmsub_rename_tac `bir_eval_cast BIExp_LowCast (SOME x')`
  >> Cases_on `x'`
  >> fs[bir_expTheory.bir_eval_cast_def]
QED

(* the spinlock_var is 0w initially *)

Theorem core_runs_spinlock_spinlock_var_default_value:
  !tr i cid t p st x. wf_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ HD tr) cid = SOME $ Core cid p st
  /\ st.bst_environ = BEnv x
  ==> x $ bir_var_name spinlock_var = SOME $ BVal_Imm $ Imm64 0w
Proof
  rpt gen_tac >> strip_tac
  >> gvs[core_runs_spinlock_def,core_runs_prog_def,spinlock_var_def]
  >> fs[bir_envTheory.bir_env_default_def,varset_of_spinlock_prog,bir_envTheory.bir_envty_of_vs_def]
  >> dsimp[bir_envTheory.bir_var_name_def,bir_valuesTheory.bir_default_value_of_type_def,bir_envTheory.bir_var_type_def,bir_immTheory.n2bs_def]
QED

(* each exclusive read reads from a certain memory location *)
(* TODO define the written value v *)
Theorem core_runs_spinlock_is_read_xcl_memory_location:
  !tr i cid t p st x. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st
  ==> bir_eval_exp (BExp_Den spinlock_var) st.bst_environ
    = SOME $ (EL (PRE t) $ SND $ EL i tr).loc
    /\ ?v. (EL (PRE t) $ SND $ EL i tr).val = BVal_Imm v
Proof
  cheat
  (*
  rpt gen_tac >> strip_tac
  >> dxrule_at_then (Pat `is_fulfil _ _ _`) assume_tac is_read_parstep_nice_eq
  >> drule_at Any wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ drule_at_then Any assume_tac
  >> gvs[is_fulfil_xcl_def,FLOOKUP_UPDATE,bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ]
  >> qhdtm_x_assum `is_certified` kall_tac
  >> qpat_x_assum `FST _ = _` kall_tac
  >> fs[bir_expTheory.bir_eval_exp_def,bir_eval_exp_view_def,bir_envTheory.bir_env_read_def]
  >> BasicProvers.every_case_tac
  >> fs[bir_expTheory.bir_eval_cast_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_name_def]
  >> qmatch_asmsub_rename_tac `bir_env_lookup "x0" st.bst_environ`
  >> Cases_on `bir_env_lookup "x0" st.bst_environ`
  >> gs[bir_expTheory.bir_eval_cast_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_name_def]
  >> qmatch_asmsub_rename_tac `bir_eval_cast BIExp_LowCast (SOME x')`
  >> Cases_on `x'`
  >> fs[bir_expTheory.bir_eval_cast_def]
  *)
QED

(* only one exclusive fulfil per thread can occur in a spinlock program *)

Theorem core_runs_spinlock_is_fulfil_xcl_once:
  !tr i j cid t t'. wf_trace tr /\ SUC i < LENGTH tr /\ SUC j < LENGTH tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil_xcl cid t' (FST $ EL j tr) (FST $ EL (SUC j) tr)
  ==> t = t' /\ j = i
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- cheat
  >> spose_not_then assume_tac
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> dxrule_at Any is_fulfil_once
  >> fs[]
  >> pop_assum $ irule_at Any
  >> fs[]
QED

(* an exclusive fulfil reads the default value *)

Theorem core_runs_spinlock_is_fulfil_xcl_is_read_xcl_default_value:
  !tr cid t i j p st st'. wf_trace tr /\ SUC j < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil_xcl cid t (FST $ EL j tr) (FST $ EL (SUC j) tr)
  /\ i < j
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> ?v. mem_read (SND $ EL i tr) ((EL (PRE t) (SND $ EL i tr)).loc) t
          = SOME mem_default_value
  /\ IS_SOME st'.bst_xclb /\ (THE st'.bst_xclb).xclb_time = 0
Proof
  rpt strip_tac
  >> drule wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ rev_drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> drule_at_then (Pat `is_read_xcl _ _ _ _`) assume_tac is_read_xcl_parstep_nice_eq
  >> gs[mem_read_view_def,optionTheory.IS_SOME_EXISTS,bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_state_t_accfupds]
  >> imp_res_tac $ iffLR bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ
  >> cheat
QED

(* any exclusive fulfil reads from timestamp 0 onwards *)

Theorem cores_run_spinlock_is_fulfil_xcl_initial_xclb:
  !tr cid t i s p st. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> IS_SOME st.bst_xclb /\ (THE st.bst_xclb).xclb_time = 0
Proof
  rpt gen_tac >> strip_tac
  >> dxrule_at_then (Pat `is_fulfil_xcl _ _ _ _`) assume_tac is_fulfil_xcl_is_read_xcl
  >> gvs[is_read_xcl_def]
  >> drule wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ rev_drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> qmatch_assum_rename_tac `FLOOKUP (FST $ EL (SUC j) _) cid = _`
  >> drule wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ qspecl_then [`SUC j`,`cid`] assume_tac
  >> first_x_assum $ qspec_then `SUC j` assume_tac
  >> gvs[LESS_EQ,optionTheory.IS_SOME_EXISTS]
  (* use core_runs_spinlock_is_fulfil_xcl_once *)
  >> cheat
QED

(* any exiting core must have fulfiled exclusively *)

Theorem core_runs_spinlock_bst_status_BST_JumpOutside_is_fulfil_xcl:
  !tr cid p st l. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ FLOOKUP (FST $ LAST tr) cid = SOME $ Core cid p st
  /\ st.bst_status = BST_JumpOutside l
  ==> ?i t. SUC i < LENGTH tr
    /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
Proof
  rpt strip_tac
  >> spose_not_then assume_tac
  >> imp_res_tac wf_trace_NOT_NULL
  >> fs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL]
  >> cheat
QED

(* the address of the spinlock variable does not change *)

Theorem core_runs_spinlock_memory_location_constant1:
  !tr cid t i s p st st'. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> bir_eval_exp (BExp_Den spinlock_var) st.bst_environ
    = bir_eval_exp (BExp_Den spinlock_var) st'.bst_environ
Proof
  rpt strip_tac
  >> drule_at Any wf_trace_core_runs_spinlock_FLOOKUP
  >> drule_all wf_trace_parstep_EL
  >> rw[]
  >> qmatch_asmsub_rename_tac `parstep_nice cid'`
  >> Cases_on `cid = cid'`
  >> gvs[FLOOKUP_UPDATE,parstep_cases,parstep_nice_def]
  >> gs[cstep_cases,FLOOKUP_UPDATE,clstep_cases]
  >> qhdtm_x_assum `is_certified` kall_tac
  >> qpat_x_assum `FST _ = _` kall_tac
  >> gvs[]
  >- (
    (* BirStmt_Read *)
    imp_res_tac $ iffLR bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ
    >> gvs[bir_eval_exp_view_def,bir_expTheory.bir_eval_exp_def,spinlock_var_def,bir_envTheory.bir_env_read_def,mem_read_def,mem_default_value_def,bir_envTheory.bir_env_update_def,bir_envTheory.bir_var_name_def]
    >> Cases_on `t`
    >> Cases_on `st.bst_environ`
    >> gvs[env_update_cast64_def,bir_envTheory.bir_env_update_def,bir_envTheory.bir_env_lookup_def,FLOOKUP_UPDATE,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_name_def,updateTheory.APPLY_UPDATE_THM,mem_read_def,mem_default_value_def,mem_read_aux_def]
    >> qmatch_asmsub_rename_tac `mem_read_aux _ el`
    >> Cases_on `el` >> fs[mem_read_aux_def,env_update_cast64_def]
    >> cheat
  )
  >> Cases_on `s.bst_pc.bpc_index` >> fs[]
  >> Cases_on `s.bst_pc.bpc_index < 5` >> gs[]
  >> gs[LT5]
  >> gvs[bir_eval_exp_view_def,bir_programTheory.bir_get_current_statement_def,CaseEq"option",pairTheory.ELIM_UNCURRY,bir_programTheory.bir_pc_next_def]
  >> imp_res_tac $ REWRITE_RULE[optionTheory.IS_SOME_EXISTS] $ iffLR bir_spinlock_prog_labels
  >> gs[bir_get_program_block_info_by_label',bir_programTheory.bir_pc_next_def]
  >> gs[get_fulfil_args_def]
  >> cheat
(*
bir_program_valid_stateTheory.bir_exec_stmtE_env_unchanged,
bir_program_env_orderTheory.bir_exec_stmt_fence_SAME_ENV,
bir_program_env_orderTheory.bir_exec_stmt_assume_SAME_ENV,
bir_program_env_orderTheory.bir_exec_stmt_assert_SAME_ENV,
bir_program_env_orderTheory.bir_exec_stmt_observe_SAME_ENV,
bir_program_env_orderTheory.bir_state_set_failed_SAME_ENV,
bir_program_valid_stateTheory.bir_exec_stmtE_env_unchanged,
bir_programTheory.bir_state_t_accfupds
*)
QED

(* any spinlock core only ever writes to the mutex variable memory location *)
(* TODO set correct address k  *)
Theorem cores_run_spinlock_is_fulfil_xcl_memory_location':
  !tr cid t i s p st. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> (EL (PRE t) $ SND $ EL i tr).loc = k
    /\ (EL (PRE t) $ SND $ EL i tr).cid = cid
Proof
  rpt gen_tac >> strip_tac
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> imp_res_tac is_fulfil_memory
  >> dxrule_at_then (Pos $ el 3) assume_tac is_fulfil_parstep_nice_imp
  >> dxrule_at_then (Pos $ el 3) assume_tac is_fulfil_xcl_atomic
  >> gvs[is_fulfil_xcl_def,parstep_nice_def,parstep_cases,FLOOKUP_UPDATE,cstep_cases,clstep_cases,stmt_generic_step_def]
  >> gs[]
  >> cheat
QED

(* all spinlock cores write to the same location *)
(* TODO set correct address k  *)
Theorem cores_run_spinlock_unique_loc:
  !tr i x. wf_trace tr /\ i < LENGTH tr
  /\ cores_run_spinlock (FST $ HD tr)
  /\ MEM x $ SND $ EL i tr
  ==> x.loc = k
Proof
  rpt strip_tac
  >> cheat
  (*
use thm core_runs_spinlock_is_fulfil_xcl_memory_location
  >> Induct_on `LENGTH $ SND $ EL i tr`
  >> rw[EVERY_MEM,MEM_EL]
  >> Cases_on `i = 0`
  >- (rw[] >> gvs[wf_trace_def,NULL_EQ])
  >> qmatch_assum_rename_tac `i < LENGTH tr`
  >> drule wf_trace_EL_SND_is_promise
  >> rpt $ disch_then drule
  >> drule_then (qspec_then `PRE i` assume_tac) wf_trace_parstep_EL
  >> qmatch_asmsub_rename_tac `MEM x $ SND $ EL i tr`
  >> gs[NOT_ZERO_LT_ZERO,AND_IMP_INTRO]
  >> first_x_assum $ drule_at Any
*)
QED

(* distinct exclusive fulfils enforce an ordering on their timestamps *)
(* TODO replace "_xcl" assumptions with t and t' have same address *)
Theorem core_runs_spinlock_is_fulfil_xcl_timestamp_order:
  !tr cid cid' t t' i j i' j'. wf_trace tr
  /\ cores_run_spinlock (FST $ HD tr)
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ core_runs_spinlock cid' (FST $ HD tr)
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil_xcl cid' t' (FST $ EL i' tr) (FST $ EL (SUC i') tr)
  /\ is_promise cid t (EL j tr) (EL (SUC j) tr)
  /\ is_promise cid' t' (EL j' tr) (EL (SUC j') tr)
  /\ i <> i' /\ j < i /\ j' < i' /\ SUC i' < LENGTH tr /\ SUC i < LENGTH tr
  ==> ~(t < t')
Proof
  rpt strip_tac
  >> `cid <> cid'` by (
    spose_not_then assume_tac
    >> gvs[]
    >> dxrule core_runs_spinlock_is_fulfil_xcl_once
    >> rpt $ disch_then $ dxrule_at Any
    >> fs[]
  )
  >> drule_at_then (Pos $ el 4) assume_tac cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> rev_drule_at_then (Pos $ el 4) assume_tac cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> drule_at_then (Pat `is_fulfil_xcl _ _ _ _`) assume_tac is_fulfil_xcl_atomic
  >> rev_drule_at_then (Pat `is_fulfil_xcl _ _ _ _`) assume_tac is_fulfil_xcl_atomic
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> gs[is_fulfil_xcl_def,optionTheory.IS_SOME_EXISTS]
  >> rev_drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> gvs[bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ]
  >> qmatch_assum_rename_tac `fulfil_atomic_ok (SND $ EL i' tr) _ cid' _ t'`
  >> qmatch_assum_rename_tac `fulfil_atomic_ok (SND $ EL i tr) _ cid _ t`
  >> `(EL (PRE t) (SND $ EL i tr)).loc = k /\ (EL (PRE t') (SND $ EL i' tr)).loc = k` by (
    ntac 2 $ dxrule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_to_memory
    >> drule cores_run_spinlock_unique_loc
    >> disch_then $ (fn x =>
      qspecl_then [`k`,`i'`,`EL (PRE t') $ SND $ EL i' tr`] assume_tac x
      >> qspecl_then [`k`,`i`,`EL (PRE t) $ SND $ EL i tr`] assume_tac x
    )
    >> gvs[EL_MEM]
  )
  >> drule cores_run_spinlock_unique_loc
  >> disch_then $ (fn x =>
    qspecl_then [`k`,`i'`,`HD $ SND $ EL i' tr`] assume_tac x
    >> qspecl_then [`k`,`i`,`HD $ SND $ EL i tr`] assume_tac x
  )
  >> drule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_to_memory
  >> rev_drule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_to_memory
  (* contradiction with atomic predicate and exclusivity bank *)
  >> `0 < LENGTH $ SND $ EL i' tr /\ 0 < LENGTH $ SND $ EL i tr` by (
    fs[is_promise_def]
    >> drule wf_trace_IS_PREFIX_SND_EL
    >> disch_then $ (fn x =>
      qspecl_then [`SUC j`,`SUC i`] assume_tac x
      >> qspecl_then [`SUC j'`,`SUC i'`] assume_tac x
    )
    >> gs[IS_PREFIX_APPEND]
    >> cheat (* minor *)
  )
  >> gs[fulfil_atomic_ok_def,Excl"EL",GSYM EL,Excl"EL_restricted",EL_MEM]
  >> last_x_assum $ qspec_then `t` assume_tac
  >> gs[GSYM PRE_SUB1]
  >> cheat (* minor *)
QED

(* Theorem 5 only one core can leave the lock region *)
Theorem core_runs_spinlock_correct:
  !tr cid cid' t i s p p' st st' l l'. wf_trace tr
  /\ cores_run_spinlock $ FST $ HD tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ core_runs_spinlock cid' $ FST $ HD tr
  /\ FLOOKUP (FST $ LAST tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ LAST tr) cid' = SOME $ Core cid' p' st'
  /\ st.bst_status = BST_JumpOutside l
  /\ st'.bst_status = BST_JumpOutside l'
  ==> cid = cid'
Proof
  rpt strip_tac
  >> drule_then assume_tac wf_trace_NOT_NULL
  >> drule_then drule core_runs_spinlock_bst_status_BST_JumpOutside_is_fulfil_xcl
  >> rpt $ disch_then $ dxrule
  >> drule_then rev_drule core_runs_spinlock_bst_status_BST_JumpOutside_is_fulfil_xcl
  >> rpt $ disch_then $ dxrule
  >> rw[]
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> Cases_on `i = i'`
  >- (
    dxrule is_fulfil_same
    >> gvs[]
    >> rpt $ disch_then dxrule
    >> fs[]
  )
  >> Cases_on `t = t'`
  >- (
    Cases_on `i < i'`
    >> dxrule is_fulfil_once
    >> disch_then $ dxrule_at_then (Pos $ el 2) assume_tac >> gs[LESS_EQ]
  )
  >> ntac 2 $ drule_then (dxrule_at Any) is_fulfil_is_promise
  >> rw[]
  >> qmatch_assum_rename_tac `is_promise cid' t' (EL jj tr) _`
  >> qmatch_assum_rename_tac `is_promise cid t (EL j tr) _`
  >> qmatch_assum_rename_tac `jj < ii`
  >> qmatch_assum_rename_tac `j < i`
  >> Cases_on `jj = j`
  >- (
    gvs[]
    >> dxrule is_promise_same
    >> rpt $ disch_then dxrule
    >> fs[]
  )
  >> drule_then drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
  >> disch_then $ rev_drule
  >> rpt $ disch_then $ drule
  >> drule_then drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
  >> disch_then $ drule
  >> disch_then $ rev_drule
  >> rpt $ disch_then $ drule
  >> fs[]
QED

val _ = export_theory();
