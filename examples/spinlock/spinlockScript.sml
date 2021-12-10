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
    ==> ?new_viewenv new_env p s v v_data v_addr l e a_e v_e var.
    SOME new_viewenv = fulfil_update_viewenv p s (is_xcl_write p s.bst_pc) t
    /\ SOME new_env = fulfil_update_env p s (is_xcl_write p s.bst_pc)
    /\ s.bst_coh l < t
    /\ (if is_xcl_write p s.bst_pc then get_xclb_view s.bst_xclb else 0) < t
    /\ s.bst_v_CAP < t
    /\ s.bst_v_wNew < t
    /\ v_data < t
    /\ v_addr < t
    /\ 0 < t
    /\ t < LENGTH (SND (EL (SUC i) tr)) + 1
    /\ EL (PRE t) (SND (EL (SUC i) tr)) = <|loc := l; val := v; cid := cid|>
    /\ (is_xcl_write p s.bst_pc ==> fulfil_atomic_ok (SND (EL (SUC i) tr)) l cid s t)
    /\ (SOME v,v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    /\ (SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\ get_fulfil_args e = SOME (a_e,v_e)
    /\ bir_get_current_statement p s.bst_pc = SOME (BStmtB (BStmt_Assign var e))
    /\ atomicity_ok cid (FST (EL i tr))
    /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
    /\ FST (EL (SUC i) tr) = FST (EL i tr) |+
        (cid,
         Core cid p
           (s with
            <|bst_pc :=
                if is_xcl_write p s.bst_pc
                then bir_pc_next (bir_pc_next (bir_pc_next s.bst_pc))
                else bir_pc_next s.bst_pc; bst_environ := new_env;
              bst_viewenv := new_viewenv;
              bst_coh :=
                (λlo. if lo = l then MAX (s.bst_coh l) t else s.bst_coh lo);
              bst_v_wOld := MAX s.bst_v_wOld t;
              bst_v_CAP := MAX s.bst_v_CAP v_addr;
              bst_prom updated_by FILTER (λt'. t' <> t);
              bst_fwdb :=
                (λlo.
                     if lo = l then
                       <|fwdb_time := t; fwdb_view := MAX v_addr v_data;
                         fwdb_xcl := is_xcl_write p s.bst_pc |>
                     else s.bst_fwdb lo);
              bst_xclb := if is_xcl_write p s.bst_pc then NONE else s.bst_xclb|>))
    /\ SND (EL i tr) = SND (EL (SUC i) tr)
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
  >> imp_res_tac is_xcl_read_is_xcl_write >> gvs[]
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
  >> imp_res_tac is_xcl_read_is_xcl_write
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
      >> imp_res_tac is_xcl_read_is_xcl_write >> fs[]
    )
    (* promises *)
    >> spose_not_then assume_tac
    >> gvs[FLOOKUP_UPDATE]
    >> fs[mem_msg_t_component_equality]
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
  >> imp_res_tac is_xcl_read_is_xcl_write >> fs[]
  >> spose_not_then assume_tac
  >> gvs[bir_get_stmt_def,AllCaseEqs()]
QED

Theorem is_promise_is_fulfil:
  !i j tr cid t. wf_trace tr /\ SUC i < LENGTH tr
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
  !i tr k cid. wf_trace tr /\ i < LENGTH tr
  /\ k < LENGTH $ SND $ EL i tr
  /\ (EL k $ SND $ EL i tr).cid = cid
  ==> ?j. j < i /\ is_promise cid (SUC k) (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_adds_to_memory
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
  ntac 3 gen_tac
  >> Induct_on `j - i` >> fs[]
  >> rw[SUB_LEFT_EQ]
  >> first_x_assum $ qspecl_then [`v + i`,`i`] assume_tac
  >> Cases_on `0 < v`
  >> gs[]
  >- (
    first_x_assum drule
    >> cheat
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
  ?st st' p var e a_e.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ is_xcl_read p st.bst_pc a_e
    /\ bir_get_current_statement p st.bst_pc =
        SOME $ BStmtB $ BStmt_Assign var e
End

Definition is_fulfil_xcl_def:
  is_fulfil_xcl cid t sys1 sys2 <=>
  ?st st' p var e.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
    /\ is_xcl_write p st.bst_pc
    /\ IS_SOME st.bst_xclb
    /\ bir_get_current_statement p st.bst_pc =
        SOME $ BStmtB $ BStmt_Assign var e
End

Theorem is_fulfil_xcl_is_fulfil:
  !cid t sys1 sys2. is_fulfil_xcl cid t sys1 sys2 ==> is_fulfil cid t sys1 sys2
Proof
  rw[is_fulfil_xcl_def,is_fulfil_def]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem is_fulfil_xcl_atomic:
  !tr i cid t p st.  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> fulfil_atomic_ok (SND $ EL i tr) ((EL (PRE t) $ SND $ EL i tr).loc) cid st t
    /\ is_xcl_write p st.bst_pc
Proof
  rpt strip_tac
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> drule_at Any is_fulfil_parstep_nice_imp
  >> rw[]
  >> gvs[parstep_nice_def,parstep_cases,is_fulfil_xcl_def,FLOOKUP_UPDATE]
  >> gvs[cstep_cases,parstep_nice_def,parstep_cases,clstep_cases,FLOOKUP_UPDATE,bir_programTheory.bir_state_t_accfupds]
  >> imp_res_tac is_xcl_read_is_xcl_write >> fs[]
  >> gvs[FLOOKUP_UPDATE,stmt_generic_step_def,bir_get_stmt_def,AllCaseEqs()]
  >- (
    drule_at Any FILTER_NEQ_NOT_MEM
    >> fs[EQ_SYM_EQ]
  )
  >- (
    drule_at Any FILTER_NEQ_NOT_MEM
    >> impl_tac
    >- (
      CONV_TAC $ RATOR_CONV $ ONCE_DEPTH_CONV SYM_CONV
      >> fs[]
    )
    >> fs[]
  )
  >- (
    dxrule_at_then Any (drule_at Any) FILTER_NEQ_MEM_EQ
    >> impl_tac
    >- (
      CONV_TAC $ RATOR_CONV $ ONCE_DEPTH_CONV SYM_CONV
      >> CONV_TAC $ RAND_CONV $ ONCE_DEPTH_CONV SYM_CONV
      >> fs[]
    )
    >> rw[]
    >> fs[]
  )
  >- (
    drule_at Any FILTER_NEQ_NOT_MEM
    >> impl_tac
    >- (
      CONV_TAC $ RATOR_CONV $ ONCE_DEPTH_CONV SYM_CONV
      >> fs[]
    )
    >> fs[]
  )
  >> drule_then (drule_then assume_tac) is_fulfil_memory
  >> gs[]
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
    gvs[bir_get_stmt_def,AllCaseEqs()]
    >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def]
    >> goal_assum $ drule_at Any
  )
  >- (
    fs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def]
    >> BasicProvers.every_case_tac
    >> fs[Once EQ_SYM_EQ]
  )
  >> qmatch_assum_rename_tac `bir_exec_stmt p stmt s = _`
  >> Cases_on `stmt`
  >- (
    qmatch_assum_rename_tac `bir_exec_stmt p (BStmtB b) s = _`
    >> Cases_on `b`
    >> fs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def,bir_programTheory.bir_state_is_terminated_def,bir_programTheory.bir_exec_stmtB_def]
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
  >> cheat
QED

(*
 * correctness of spinlock
 *)

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

(* Theorem 4 : any exclusive fulfil reads from timestamp 0 onwards *)

Theorem cores_run_spinlock_is_fulfil_xcl_initial_xclb:
  !tr cid t i s p st. wf_trace tr /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> IS_SOME st.bst_xclb /\ (THE st.bst_xclb).xclb_time = 0
Proof
  cheat
QED

(* any exiting core must have fulfiled exclusively *)

Theorem core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl:
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

(*
TODO formulate theorem: (forward reasoning)
any core running the spinlock can only have one is_fulfil_xcl transition
*)

(* distinct exclusive fulfils enforce an ordering on their timestamps *)
(* TODO replace "_xcl" assumptions with t and t' have same address *)
Theorem core_runs_spinlock_is_fulfil_xcl_timestamp_order:
  !tr cid cid' t t' i j i' j'. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ core_runs_spinlock cid' (FST $ HD tr)
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil_xcl cid' t' (FST $ EL i' tr) (FST $ EL (SUC i') tr)
  /\ is_promise cid t (EL j tr) (EL (SUC j) tr)
  /\ is_promise cid' t' (EL j' tr) (EL (SUC j') tr)
  /\ i <> i' /\ j < i /\ j' < i' /\ SUC i' < LENGTH tr
  ==> ~(t < t')
Proof
  rpt strip_tac
  >> drule_then (rev_drule_then $ drule_then assume_tac)
    cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> drule_then (rev_drule_at_then Any assume_tac)
    cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> `cid <> cid'` by (
    spose_not_then assume_tac
    >> gvs[]
    >> first_x_assum $ rev_drule_at_then Any assume_tac
    >> last_x_assum $ drule_at_then Any assume_tac
    >> cheat
  )
  >> fs[is_fulfil_xcl_def]
  (* contradiction with atomic predicate and exclusivity bank *)
  >> cheat
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
  >> drule_then drule core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl
  >> rpt $ disch_then $ dxrule
  >> drule_then rev_drule core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl
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
  >> `~(t < t')` by (
    drule_then rev_drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
    >> rpt $ disch_then drule
    >> fs[]
  )
  >> `~(t' < t)` by (
    drule_then drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
    >> rpt $ disch_then rev_drule
    >> fs[]
  )
  >> fs[]
QED

val _ = export_theory();
