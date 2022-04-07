open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = new_theory "tracestep";

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory tracesTheory;
open finite_mapTheory;

Theorem IS_PREFIX_EL:
  !l2 l1 n. IS_PREFIX l2 l1 /\ n < LENGTH l1
  ==> EL n l1 = EL n l2
Proof
  fs[IS_PREFIX_APPEND,EL_APPEND1,PULL_EXISTS]
QED

Theorem LT3 =
  (REWRITE_CONV [GSYM rich_listTheory.COUNT_LIST_COUNT,
    GSYM pred_setTheory.IN_COUNT]
    THENC EVAL) ``n < 3n``

Theorem LT5 =
  (REWRITE_CONV [GSYM rich_listTheory.COUNT_LIST_COUNT,
    GSYM pred_setTheory.IN_COUNT]
    THENC EVAL) ``n < 5n``

(*
 * equality of projection of states
 *)

Definition same_state_prop_def:
  same_state_prop cid st1 st2 f =
    !p p' st st'.
      FLOOKUP st1 cid = SOME $ Core cid p st
      /\ FLOOKUP st2 cid = SOME $ Core cid p' st'
      ==> f st = f st'
End

Definition same_state_prop_range_def:
  same_state_prop_range cid tr i j f <=>
    i <= j /\ !k. i <= k /\ k < j
      ==> same_state_prop cid (FST $ EL k tr) (FST $ EL (SUC k) tr) f
End

Theorem same_state_prop_range_add:
  same_state_prop_range cid tr i j f
  /\ same_state_prop_range cid tr j k f
  ==> same_state_prop_range cid tr i k f
Proof
  rw[same_state_prop_range_def]
  >> qmatch_assum_rename_tac `kk < k`
  >> Cases_on `j <= kk`
  >- (first_x_assum irule >> fs[])
  >> fs[NOT_LESS_EQUAL]
QED

Theorem same_state_prop_range_SUC:
  same_state_prop_range cid tr i (SUC j) f
  /\ i <= j
  ==> same_state_prop_range cid tr i j f
Proof
  rw[same_state_prop_range_def]
QED

Theorem same_state_prop_range_prop:
  wf_trace tr /\ SUC k < LENGTH tr
  /\ same_state_prop_range cid tr i (SUC k) f
  /\ same_state_prop cid (FST (EL i tr)) (FST $ EL k tr) f
  ==> same_state_prop cid (FST (EL i tr)) (FST (EL (SUC k) tr)) f
Proof
  rw[same_state_prop_def,same_state_prop_range_def]
  >> drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac wf_trace_cid_backward1
  >> dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >> gvs[PULL_FORALL,AND_IMP_INTRO]
  >> first_x_assum $ drule_at $ Pat `FLOOKUP _ _ = _`
  >> fs[]
QED

Theorem same_state_prop_indexes:
  !i j cid tr f.
  wf_trace tr /\ j < LENGTH tr
  /\ same_state_prop_range cid tr i j f
  ==> same_state_prop cid (FST $ EL i tr) (FST $ EL j tr) f
Proof
  rpt gen_tac
  >> Induct_on `j - i`
  >> rpt strip_tac
  >- (
    fs[same_state_prop_range_def,relationTheory.reflexive_def]
    >> dxrule_all_then assume_tac $ iffLR $ GSYM arithmeticTheory.EQ_LESS_EQ
    >> rw[same_state_prop_def]
    >> gs[]
  )
  >> gvs[AND_IMP_INTRO,Once SUB_LEFT_EQ]
  >> first_x_assum $ qspecl_then [`i+v`,`i`] mp_tac
  >> impl_tac
  >- (
    fs[]
    >> irule same_state_prop_range_SUC
    >> fs[ADD1]
  )
  >> strip_tac
  >> drule_at (Pat `same_state_prop _ _ _ _`) same_state_prop_range_prop
  >> fs[ADD1]
QED

(*
 * characterisation of fulfil and promise rules
 *)

Definition is_fulfil_def:
  is_fulfil cid t sys1mem sys2 =
  ?st st' p var e.
    FLOOKUP (FST sys1mem) cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
    /\ bir_get_current_statement p st.bst_pc =
        SOME $ BStmtB $ BStmt_Assign var e
    /\ PRE t < LENGTH $ SND $ sys1mem
    /\ 0 < t
    /\ (EL (PRE t) $ SND $ sys1mem).cid = cid
End

Theorem is_fulfil_MEM_bst_prom:
  !cid t sys1 sys2. is_fulfil cid t sys1 sys2
  ==> ?p st. FLOOKUP (FST sys1) cid = SOME $ Core cid p st /\ MEM t st.bst_prom
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
  ==> parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all is_fulfil_parstep_nice
  >> fs[]
QED

Theorem is_fulfil_memory:
  !tr i cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
    /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
    ==>  ?p s var xcl e v_e v_data v_addr v l new_viewenv new_env a_e rel_acq rel acq.
      bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel
    /\ xcl = is_xcl_write p s.bst_pc
    /\ rel = is_rel p s.bst_pc
    /\ acq = is_acq p s.bst_pc
    /\ rel_acq = (rel /\ acq)
    /\  MEM t s.bst_prom
    /\  bir_get_current_statement p s.bst_pc =
        SOME (BStmtB (BStmt_Assign var e))
    /\  get_fulfil_args e = SOME (a_e,v_e)
    /\  EL (PRE t) (SND (EL (SUC i) tr)) = <|loc := l; val := v; cid := cid|>
    /\  (xcl ==> fulfil_atomic_ok (SND (EL (SUC i) tr)) l cid s t)
    /\  t < LENGTH (SND (EL (SUC i) tr)) + 1
    /\  (SOME v,v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    /\  (SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\  (if acq /\ rel /\ xcl then s.bst_v_Rel else 0) < t
    /\  (if rel then MAX s.bst_v_rOld s.bst_v_wOld else 0) < t
    /\  SOME new_viewenv =
        fulfil_update_viewenv p s xcl t
    /\  (if xcl then get_xclb_view s.bst_xclb else 0) < t
    /\  SOME new_env = fulfil_update_env p s xcl
    /\  s.bst_coh l < t
    /\  s.bst_v_wNew < t
    /\  s.bst_v_CAP < t
    /\  v_data < t
    /\  v_addr < t
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
              bst_v_rNew :=
                if
                  acq /\ rel /\
                  xcl
                then
                  MAX s.bst_v_rNew t
                else s.bst_v_rNew;
              bst_v_wNew :=
                if
                  acq /\ rel /\
                  xcl
                then
                  MAX s.bst_v_wNew t
                else s.bst_v_wNew; bst_v_CAP := MAX s.bst_v_CAP v_addr;
              bst_v_Rel :=
                MAX s.bst_v_Rel
                  (if acq /\ rel then t else 0);
              bst_prom updated_by FILTER (λt'. t' <> t);
              bst_fwdb :=
                (λlo.
                     if lo = l then
                       <|fwdb_time := t; fwdb_view := MAX v_addr v_data;
                         fwdb_xcl := xcl |>
                     else s.bst_fwdb lo);
              bst_xclb :=
                if xcl then NONE else s.bst_xclb|>))
    /\  FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p s)
Proof
  rpt strip_tac
  >> drule_all_then assume_tac is_fulfil_parstep_nice_imp
  >> drule_all_then assume_tac is_fulfil_memory
  >> gvs[parstep_nice_def,parstep_cases,clstep_cases,cstep_cases,is_fulfil_def,FLOOKUP_UPDATE,bir_programTheory.bir_state_t_accfupds,stmt_generic_step_def,bir_get_stmt_branch,bir_get_stmt_generic,FILTER_EQ_ID,EVERY_MEM,AC CONJ_ASSOC CONJ_COMM,FUPD11_SAME_KEY_AND_BASE]
  >> dxrule_at_then Any (drule_at Any) FILTER_NEQ_MEM_EQ
  >> impl_tac
  >- (
    CONV_TAC $ RATOR_CONV $ ONCE_DEPTH_CONV SYM_CONV
    >> CONV_TAC $ RAND_CONV $ ONCE_DEPTH_CONV SYM_CONV
    >> fs[]
  )
  >> disch_then $ fs o single
  >> gvs[bir_get_stmt_write]
  >> rpt $ goal_assum $ rev_drule_at Any
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ ~is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
    /\ is_fulfil cid t (EL j tr) (FST $ EL (SUC j) tr)
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
  ==> 0 < t /\ t < (LENGTH $ SND $ EL (SUC i) tr) + 1
    /\ (EL (PRE t) $ SND $ EL (SUC i) tr).cid = cid
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then strip_assume_tac is_fulfil_parstep_nice_eq
  >> gs[arithmeticTheory.PRE_SUB1]
QED

(* a fulfil is only fulfilled once *)

Theorem is_fulfil_once:
  !tr i j t cid cid'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC j < LENGTH tr /\ i <> j
  ==> ~is_fulfil cid' t (EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> wlog_tac `i < j` [`i`,`j`,`cid`,`cid'`]
  >- metis_tac[NOT_NUM_EQ,LESS_EQ]
  >> qmatch_assum_rename_tac `is_fulfil cid t (EL i tr) _`
  >> qmatch_assum_rename_tac `is_fulfil cid' t (EL j tr) _`
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
  >> qmatch_assum_abbrev_tac `cid = _.cid`
  >> qspecl_then [`SUC i`,`j`,`tr`,`cid`] assume_tac
    wf_trace_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom
  >> gs[EVERY_MEM,AND_IMP_INTRO,Abbr`cid`]
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil cid' t' (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  is_read_xcl cid t sys1mem sys2 <=>
  ?st st' p var a_e cast_opt acq rel.
    FLOOKUP (FST sys1mem) cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ bir_get_stmt p st.bst_pc = BirStmt_Read var a_e cast_opt T acq rel
    /\ IS_SOME st'.bst_xclb
    /\ (THE st'.bst_xclb).xclb_time = t
    /\ IS_NONE st.bst_xclb
    /\ (0 < t
      ==>
        PRE t < LENGTH $ SND sys1mem
        /\ (EL (PRE t) $ SND sys1mem).cid = cid)
End

Definition is_fulfil_xcl_def:
  is_fulfil_xcl cid t sys1mem sys2 <=>
  ?st st' p a_e v_e acq rel.
    FLOOKUP (FST sys1mem) cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
    /\ bir_get_stmt p st.bst_pc = BirStmt_Write a_e v_e T acq rel
    /\ IS_SOME st.bst_xclb
    /\ PRE t < LENGTH $ SND $ sys1mem
    /\ 0 < t
    /\ (EL (PRE t) $ SND $ sys1mem).cid = cid
End

Theorem is_fulfil_xcl_is_fulfil:
  !cid t sys1mem sys2. is_fulfil_xcl cid t sys1mem sys2
  ==> is_fulfil cid t sys1mem sys2
Proof
  rw[is_fulfil_xcl_def,is_fulfil_def,bir_get_stmt_write]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem is_fulfil_xcl_atomic:
  !tr i cid t p st.  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> fulfil_atomic_ok (SND $ EL (SUC i) tr)
        ((EL (PRE t) $ SND $ EL (SUC i) tr).loc) cid st t
    /\ is_xcl_write p st.bst_pc
    /\  (EL (PRE t) $ SND $ EL (SUC i) tr).cid = cid
Proof
  rpt gen_tac >> strip_tac
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> drule_at_then Any assume_tac is_fulfil_parstep_nice_eq
  >> gvs[is_fulfil_xcl_def,bir_get_stmt_write]
QED

(* parstep and read transitions have same ids *)

Theorem is_read_xcl_parstep_nice:
  !tr i cid cid' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_read_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
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
  /\ is_read_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
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
    /\ is_read_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
    ==> ?p s st' opt_cast ν_pre v_addr new_env l a_e var v zcq rel acq.
    is_certified p cid st' (SND (EL (SUC i) tr))
    /\ st' = (s with
           <|bst_pc := bir_pc_next (bir_pc_next s.bst_pc);
             bst_environ := new_env;
             bst_viewenv updated_by
               (\env. env |+ (var,
                     MAX (MAX (MAX (MAX v_addr s.bst_v_rNew)
                             (if acq /\ rel then s.bst_v_Rel else 0))
                          (if acq /\ rel then MAX s.bst_v_rOld s.bst_v_wOld
                           else 0)) (mem_read_view (s.bst_fwdb l) t)));
             bst_coh :=
               (\lo.
                    if lo = l then
                      MAX (s.bst_coh l) $ MAX (MAX
                              (MAX (MAX v_addr s.bst_v_rNew)
                                 (if acq /\ rel then s.bst_v_Rel else 0))
                              (if acq /\ rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                          (mem_read_view (s.bst_fwdb l) t)
                    else s.bst_coh lo);
             bst_v_rOld :=
               MAX s.bst_v_rOld
                 (MAX (MAX (MAX (MAX v_addr s.bst_v_rNew)
                          (if acq /\ rel then s.bst_v_Rel else 0))
                       (if acq /\ rel then MAX s.bst_v_rOld s.bst_v_wOld
                        else 0)) (mem_read_view (s.bst_fwdb l) t));
             bst_v_rNew :=
               if acq then
                 MAX s.bst_v_rNew
                   (MAX (MAX (MAX (MAX v_addr s.bst_v_rNew)
                            (if rel then s.bst_v_Rel else 0))
                         (if rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                      (mem_read_view (s.bst_fwdb l) t))
               else s.bst_v_rNew;
             bst_v_wNew :=
               if acq then
                 MAX s.bst_v_wNew
                   (MAX (MAX (MAX (MAX v_addr s.bst_v_rNew)
                            (if rel then s.bst_v_Rel else 0))
                         (if rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                      (mem_read_view (s.bst_fwdb l) t))
               else s.bst_v_wNew; bst_v_CAP := MAX s.bst_v_CAP v_addr;
             bst_v_Rel :=
               MAX s.bst_v_Rel
                 (if rel /\ acq then
                    MAX (MAX (MAX (MAX v_addr s.bst_v_rNew) s.bst_v_Rel)
                         (MAX s.bst_v_rOld s.bst_v_wOld))
                      (mem_read_view (s.bst_fwdb l) t)
                  else 0);
             bst_xclb :=
               SOME
                 <|xclb_time := t;
                   xclb_view :=
                     MAX (MAX (MAX (MAX v_addr s.bst_v_rNew)
                             (if acq /\ rel then s.bst_v_Rel else 0))
                          (if acq /\ rel then MAX s.bst_v_rOld s.bst_v_wOld
                           else 0)) (mem_read_view (s.bst_fwdb l) t)|> |>)
    /\  SOME new_env =
        env_update_cast64 (bir_var_name var) v (bir_var_type var) s.bst_environ
    /\  (!t''. t < t'' /\ (t'' <= ν_pre \/ t'' <= s.bst_coh l) ==>
          (EL t'' (SND (EL i tr))).loc <> l)
    /\  mem_read (SND (EL i tr)) l t = SOME v
    /\  (SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    /\  bir_get_stmt p s.bst_pc = BirStmt_Read var a_e opt_cast T acq rel
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
  ==> ?t. is_read_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,parstep_cases,DISJ_EQ_IMP]
  >> reverse $ Cases_on `cid = cid'`
  >> gvs[FLOOKUP_UPDATE,clstep_cases,cstep_cases,parstep_nice_def,parstep_cases,is_read_xcl_def,optionTheory.IS_SOME_EXISTS]
  >> cheat
QED

(* a successful exclusive store has an earlier exclusive load *)
(* TODO encode success *)
Theorem is_fulfil_xcl_is_read_xcl:
  !i tr cid p st t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> ?j. j < i
    /\ is_read_xcl cid t (EL j tr) (FST $ EL (SUC j) tr)
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
    >> `is_read_xcl cid t (EL (LENGTH tr - n) tr) (FST (EL (SUC $ LENGTH tr - n) tr))` by (
      irule xclb_NONE_SOME_is_read_xclb
      >> fs[]
    )
    >> goal_assum $ drule_at Any
    (* TODO by xclb_NONE_SOME_is_read_xclb, this is an exclusive load *)
    >> cheat
  )
  >> cheat
QED

(* fence transitions and their properties *)

Definition is_fence_def:
  is_fence cid K1 K2 sys1 sys2 <=>
  ?st st' p.
    FLOOKUP sys1 cid = SOME $ Core cid p st
    /\ FLOOKUP sys2 cid = SOME $ Core cid p st'
    /\ bir_get_stmt p st.bst_pc = BirStmt_Fence K1 K2
    /\ st'.bst_pc = bir_pc_next st.bst_pc
    /\ st'.bst_prom = st.bst_prom
End

Theorem is_fence_parstep_nice:
  !tr i cid K1 K2.
    wf_trace tr /\ SUC i < LENGTH tr
    /\ is_fence cid K1 K2 (FST $ EL i tr) (FST $ EL (SUC i) tr)
    ==> parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> spose_not_then assume_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> Cases_on `cid = cid'`
  >> fs[]
  >> drule wf_trace_NOT_parstep_nice_state_EQ'
  >> rpt $ disch_then $ drule
  >> gs[is_fence_def,bir_programTheory.bir_state_t_accfupds,bir_programTheory.bir_pc_next_def,bir_programTheory.bir_programcounter_t_component_equality,parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
QED

Theorem is_fence_RW_W_post:
  !tr i j cid p st st'.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fence cid BM_ReadWrite BM_Write (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==>
    st'.bst_v_rNew = st.bst_v_rNew
    /\ st'.bst_v_wNew = MAX st.bst_v_wNew $ MAX st.bst_v_rOld st.bst_v_wOld
Proof
  rpt gen_tac >> strip_tac
  >> drule_at_then (Pat `is_fence _ _ _ _ _`) assume_tac is_fence_parstep_nice
  >> gvs[is_fence_def,parstep_nice_def,parstep_cases,cstep_cases,bir_programTheory.bir_state_t_accfupds,FLOOKUP_UPDATE,clstep_cases,is_read_def,is_write_def]
QED

(* exclusive bank semantics *)

(*
 * two distinct cores cid, cid' cannot exclusively fulfil to the same address
 * if the lr/sc are interleaved.
 * Here the sc (exclusive fulfil) of cid sees the lr (exclusive read) of cid'
 *   lr_cid < lr_cid' < sc_cid
 *)
Theorem is_fulfil_xcl_is_read_xcl_is_fulfil_xcl:
  !i j tr cid cid' p st p' st' t t'. wf_trace tr
  /\ is_fulfil_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ (THE st.bst_xclb).xclb_time < t
  /\ (THE st.bst_xclb).xclb_time < LENGTH $ SND $ EL (SUC i) tr
  /\ PRE t < LENGTH $ SND $ EL (SUC i) tr
  /\ PRE (THE st.bst_xclb).xclb_time < LENGTH $ SND $ EL (SUC i) tr
  /\ (0 < (THE st.bst_xclb).xclb_time ==>
    (EL (PRE (THE st.bst_xclb).xclb_time) (SND (EL (SUC i) tr))).loc
      = (EL (PRE t) (SND (EL (SUC i) tr))).loc
    /\ (EL (PRE $ (THE st.bst_xclb).xclb_time) (SND (EL (SUC i) tr))).cid = cid)
  /\ (EL (PRE t) (SND (EL (SUC i) tr))).cid = cid
  /\ is_fulfil_xcl cid' t' (EL j tr) (FST $ EL (SUC j) tr)
  /\ SUC j < LENGTH tr
  /\ FLOOKUP (FST $ EL j tr) cid' = SOME $ Core cid' p' st'
  /\ 0 < (THE st'.bst_xclb).xclb_time
  /\ (THE st'.bst_xclb).xclb_time < t'
  /\ (THE st'.bst_xclb).xclb_time < LENGTH $ SND $ EL (SUC j) tr
  /\ PRE t' < LENGTH $ SND $ EL (SUC j) tr
  /\ (EL (PRE t') (SND (EL (SUC j) tr))).cid = cid'
  /\ (EL (PRE $ (THE st'.bst_xclb).xclb_time) (SND (EL (SUC j) tr))).cid = cid'
  /\ i < j
  /\ (EL (PRE (THE st'.bst_xclb).xclb_time) (SND (EL (SUC j) tr))).loc
    = (EL (PRE t') (SND (EL (SUC j) tr))).loc
  /\ cid <> cid'
  /\ (0 < (THE st.bst_xclb).xclb_time ==>
    (EL (PRE (THE st.bst_xclb).xclb_time) $ SND $ EL (SUC i) tr).loc
      = (EL (PRE (THE st'.bst_xclb).xclb_time) $ SND $ EL (SUC j) tr).loc)
  /\ (EL (PRE t') $ SND $ EL (SUC j) tr).loc
    = (EL (PRE t) $ SND $ EL (SUC j) tr).loc
  /\ (THE st.bst_xclb).xclb_time < (THE st'.bst_xclb).xclb_time
  /\ (THE st'.bst_xclb).xclb_time < t
  ==> F
Proof
  rpt strip_tac
  >> qmatch_assum_abbrev_tac `A ==> _`
  >> Cases_on `A` >> fs[]
  >> drule_then (qspecl_then [`SUC j`,`SUC i`] assume_tac) wf_trace_EL_SND_EQ_EL_SND
  >> drule_at_then (Pos $ el 3) assume_tac is_fulfil_xcl_atomic
  >> rev_drule_at_then (Pos $ el 3) assume_tac is_fulfil_xcl_atomic
  >> `SUC i < SUC j` by fs[]
  >> drule_all_then assume_tac wf_trace_IS_PREFIX_SND_EL
  >> gs[optionTheory.IS_SOME_EXISTS,is_fulfil_xcl_def,IS_PREFIX_APPEND]
  >> dxrule $ iffLR fulfil_atomic_ok_def
  >> fs[]
  >> qpat_x_assum `_ < _.xclb_time` $ irule_at Any
  >> gvs[GSYM arithmeticTheory.PRE_SUB1]
QED

(*
 * a successful fulfil t2 with its preceeding read t1
 *)
Definition lr_sc_def:
  lr_sc cid tr t1 i1 t2 i2 <=>
  SUC i2 < LENGTH tr
  /\ PRE t2 < LENGTH $ SND $ EL i2 tr
  /\ is_read_xcl cid t1 (EL i1 tr) (FST $ EL (SUC i1) tr)
  /\ is_fulfil_xcl cid t2 (EL i2 tr) (FST $ EL (SUC i2) tr)
  /\ i1 < i2
  /\ t1 < t2 (* view timestamps strictly ordered *)
  /\ (* exclusive bank unchanged *)
    same_state_prop_range cid tr (SUC i1) i2 (λst. st.bst_xclb)
  /\ (0 < t1 ==>
    (EL (PRE t1) $ SND $ EL (SUC i1) tr).loc
    = (EL (PRE t2) $ SND $ EL (SUC i2) tr).loc)
End

Theorem lr_sc_cid:
  !tr cid t1 i1 t2 i2.
  wf_trace tr
  /\ lr_sc cid tr t1 i1 t2 i2
  ==>
    (EL (PRE t2) $ SND $ EL (SUC i2) tr).cid = cid
    /\ (0 < t1
      ==> (EL (PRE t1) $ SND $ EL i1 tr).cid = cid)
Proof
  rpt gen_tac >> strip_tac
  >> fs[lr_sc_def]
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> dxrule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_memory
  >> gs[is_fulfil_xcl_def,is_read_xcl_def]
QED

Theorem lr_sc_bst_xclb_eq:
  !tr cid t1 i1 t2 i2.
  wf_trace tr
  /\ lr_sc cid tr t1 i1 t2 i2
  ==> same_state_prop cid (FST (EL (SUC i1) tr)) (FST (EL i2 tr)) (λst. st.bst_xclb)
Proof
  rw[lr_sc_def]
  >> irule same_state_prop_indexes
  >> fs[]
QED

Theorem lr_sc_memory:
  !tr cid t1 i1 t2 i2.
  wf_trace tr /\ lr_sc cid tr t1 i1 t2 i2
  ==> SND $ EL i2 tr = SND $ EL (SUC i2) tr
Proof
  rw[lr_sc_def]
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> drule_all_then irule is_fulfil_memory
QED

(*
 * two distinct cores cid, cid' cannot exclusively fulfil to the same address
 * if the lr/sc are interleaved (t1 < t1' < t2).
 * The exclusive fulfil to t2 of cid sees the exclusive read of cid' to t1'
 *)
Theorem lr_sc_interleaved_pair:
  !i j tr cid cid' t1 t2 i1 i2 t1' t2' j1 j2.
  wf_trace tr
  /\ lr_sc cid tr t1 i1 t2 i2
  /\ lr_sc cid' tr t1' j1 t2' j2
  /\ t1 < t1' /\ t1' < t2
  /\ cid <> cid'
  /\ i2 < j2
  /\ (EL (PRE t2) $ SND $ EL (SUC i2) tr).loc
    = (EL (PRE t2') $ SND $ EL (SUC j2) tr).loc
  ==> F
Proof
  rpt strip_tac
  >> drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_bst_xclb_eq
  >> rev_drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_bst_xclb_eq
  >> drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_cid
  >> rev_drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_cid
  >> drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_memory
  >> rev_drule_at (Pat `lr_sc _ _ _ _ _ _`) lr_sc_memory
  >> rpt strip_tac
  >> gs[]
  >> drule_then irule is_fulfil_xcl_is_read_xcl_is_fulfil_xcl
  >> rev_drule_then (irule_at Any) $ cj 4 $ iffLR lr_sc_def
  >> drule_then (irule_at Any) $ cj 4 $ iffLR lr_sc_def
  >> qspecl_then [`tr`,`SUC j1`,`SUC j2`] assume_tac wf_trace_IS_PREFIX_SND_EL'
  >> qspecl_then [`tr`,`j1`,`SUC j2`] assume_tac wf_trace_IS_PREFIX_SND_EL'
  >> qspecl_then [`tr`,`SUC i1`,`SUC i2`] assume_tac wf_trace_IS_PREFIX_SND_EL'
  >> qspecl_then [`tr`,`i1`,`SUC i2`] assume_tac wf_trace_IS_PREFIX_SND_EL'
  >> qspecl_then [`tr`,`i2`,`j2`] assume_tac wf_trace_IS_PREFIX_SND_EL'
  >> qspecl_then [`tr`,`j1`,`SUC j1`] assume_tac wf_trace_memory_LENGTH
  >> qspecl_then [`tr`,`i1`,`SUC i1`] assume_tac wf_trace_memory_LENGTH
  >> gs[lr_sc_def]
  >> Cases_on `0 < t1`
  >> gvs[same_state_prop_def,is_fulfil_xcl_def,is_read_xcl_def,IS_PREFIX_EL]
  >> conj_asm1_tac
  >- gs[IS_PREFIX_LENGTH,arithmeticTheory.PRE_SUB1]
  >> rpt $ dxrule_then assume_tac IS_PREFIX_EL
  >> gs[]
QED

val _ = export_theory();
