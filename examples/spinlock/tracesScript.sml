open HolKernel Parse boolLib bossLib;

val _ = new_theory "traces";

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory finite_mapTheory;

(*
 * general lemmata
 *)

Theorem FILTER_NEQ_MEM_EQ:
  !t t' s. FILTER ($<> t) s = FILTER ($<> t') s
  /\ MEM t s /\ MEM t' s ==> t = t'
Proof
  rpt strip_tac
  >> qmatch_assum_abbrev_tac `rhs = lhs`
  >> `EVERY ($<> t) lhs` by (
    fs[Once EQ_SYM_EQ,Abbr`rhs`,EVERY_FILTER]
  )
  >> fs[EVERY_FILTER,EVERY_MEM,Abbr`lhs`]
QED

Theorem FILTER_NEQ_NOT_MEM:
  !t s. FILTER ($<> t) s = s /\ MEM t s ==> F
Proof
  fs[] >> rpt gen_tac >> strip_tac
  >> pop_assum $ ONCE_REWRITE_TAC o single o GSYM
  >> fs[MEM_FILTER]
QED

Theorem FUPDATE_EQ:
   !s k1 v1 k2 v2. s |+ (k1,v1) = s |+ (k2,v2) /\ k1 <> k2
   ==> FLOOKUP (s |+ (k1,v1)) k2 = SOME v2
   /\ FLOOKUP (s |+ (k2,v2)) k1 = SOME v1
Proof
  rpt strip_tac
  >- (fs[] >> fs[finite_mapTheory.FLOOKUP_UPDATE])
  >> fs[Once EQ_SYM_EQ]
  >> fs[finite_mapTheory.FLOOKUP_UPDATE]
QED

(*
 * Defintion of traces
 *)

Inductive is_gen_trace:
  (!R s. is_gen_trace R [s]) /\
  (!R s2 s1 t . ((is_gen_trace R (APPEND t [s1])) /\ (R s1 s2)) ==>
                (is_gen_trace R (APPEND t [s1;s2]))
  )
End

Definition gen_traces_def:
  gen_traces R = { t | is_gen_trace R t }
End

Definition parstep_nice_def:
  parstep_nice cid s1 s2 = parstep cid (FST s1) (SND s1) (FST s2) (SND s2)
End

(* memory is monotonic only ever increases, at most by one *)

Theorem parstep_nice_memory_imp:
  !cid s1 s2. parstep_nice cid s1 s2
  ==> SND s1 = SND s2 \/ ?m. SND s2 = SND s1 ++ [m] /\ m.cid = cid
Proof
  fs[gen_traces_def,parstep_nice_def,pairTheory.FORALL_PROD]
  >> rw[cstep_cases,parstep_cases]
  >> disj2_tac
  >> rpt $ irule_at Any EQ_REFL
QED

(* future promises are larger than current memory size *)

Theorem parstep_nice_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom:
  !cid cid' sys1 sys2 p p' st st'. parstep_nice cid sys1 sys2
  /\ FLOOKUP (FST sys1) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST sys2) cid = SOME $ Core cid p st'
  ==> EVERY (λx. ~MEM x st.bst_prom ==> LENGTH (SND sys1) < x) st'.bst_prom
Proof
  rpt strip_tac
  >> gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE,cstep_cases]
  >> imp_res_tac clstep_LENGTH_prom >> gvs[]
  >- (
    imp_res_tac clstep_bst_prom_EQ
    >> fs[EVERY_MEM]
  )
  >> fs[clstep_cases,EVERY_MEM,MEM_FILTER]
QED

(* set of all traces *)
Definition par_traces_def:
  par_traces = gen_traces (λs1 s2. ?cid. parstep_nice cid s1 s2)
End

Theorem par_traces_ind:
  !P. (!s. P [s])
  /\ (!s2 s1 t. P (t ++ [s1]) /\ (?cid. parstep_nice cid s1 s2) ==> P (t ++ [s1; s2]))
  ==> !tr. tr IN par_traces ==> P tr
Proof
  fs[par_traces_def,gen_traces_def]
  >> ntac 2 strip_tac
  >> `!ps tr. is_gen_trace ps tr ==> ps = (λs1 s2. ?cid. parstep_nice cid s1 s2)
    ==> P tr` by (
    ho_match_mp_tac is_gen_trace_ind
    >> fs[AND_IMP_INTRO,PULL_FORALL,PULL_EXISTS]
  )
  >> fs[PULL_FORALL]
QED

Theorem is_gen_trace_NOT_NULL:
  !R s. is_gen_trace R s ==> ~NULL s
Proof
  ho_match_mp_tac is_gen_trace_ind
  >> fs[NULL_EQ]
QED

Theorem is_gen_trace_EL:
  !R s. is_gen_trace R s ==> !i. SUC i < LENGTH s ==> R (EL i s) (EL (SUC i) s)
Proof
  ho_match_mp_tac is_gen_trace_ind
  >> rw[]
  >> qmatch_assum_rename_tac `SUC i < LENGTH t + 2`
  >> Cases_on `SUC i < LENGTH t`
  >- (
    first_x_assum $ qspec_then `i` mp_tac
    >> fs[EL_APPEND1]
  )
  >> fs[NOT_LESS,LESS_OR_EQ]
  >- (
    `i = LENGTH t` by fs[]
    >> pop_assum $ fs o single
    >> fs[EL_APPEND1,EL_APPEND2]
  )
  >> first_x_assum $ qspec_then `i` mp_tac
  >> fs[EL_APPEND1,EL_APPEND2]
QED

(*
 * well-formed traces and implications of well-formedness
 *)

Theorem parstep_nice_EX_FLOOKUP:
  !cid s1 s2. parstep_nice cid s1 s2
  ==> ?p st. FLOOKUP (FST s1) cid = SOME (Core cid p st)
Proof
  rw[parstep_nice_def,parstep_cases] >> fs[]
QED

Theorem parstep_nice_FLOOKUP:
  !cid s1 s2 cid' p st. parstep_nice cid s1 s2
  /\ FLOOKUP (FST s1) cid' = SOME (Core cid' p st)
  ==> ?st'. FLOOKUP (FST s2) cid' = SOME (Core cid' p st')
Proof
  rpt strip_tac
  >> fs[parstep_nice_def,parstep_cases,finite_mapTheory.FLOOKUP_UPDATE]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem parstep_nice_FLOOKUP':
  !cid s1 s2 cid' p st. parstep_nice cid s1 s2
  /\ FLOOKUP (FST s1) cid' = SOME (Core cid' p st)
  /\ cid <> cid'
  ==> FLOOKUP (FST s2) cid' = SOME (Core cid' p st)
Proof
  rpt strip_tac
  >> fs[parstep_nice_def,parstep_cases,finite_mapTheory.FLOOKUP_UPDATE]
  >> fs[]
QED

Theorem parstep_nice_parstep_nice:
  !s1 s2 cid cid'.
  parstep_nice cid s1 s2 /\ parstep_nice cid' s1 s2
  ==> cid = cid'
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
  >> drule_then assume_tac FUPDATE_EQ
  >> gvs[FLOOKUP_UPDATE]
  >> `FST s2 = FST s1` by (
    rw[FUN_EQ_THM,FLOOKUP_UPDATE,FLOOKUP_EXT,Once EQ_SYM_EQ]
    >> BasicProvers.every_case_tac
    >> fs[]
  )
  >> gvs[FUPD11_SAME_BASE]
  >> ntac 2 $ qpat_x_assum `_ |+ _ = _` kall_tac
  >> fs[cstep_cases]
  >> imp_res_tac clstep_LENGTH_prom
  >> gvs[]
  >> imp_res_tac clstep_bst_prom_NOT_EQ >> fs[]
  >> cheat
QED

Definition empty_prom_def:
  empty_prom s = !cid p st.
  FLOOKUP s cid = SOME $ Core cid p st
  ==> NULL st.bst_prom
End

Definition empty_xclb_def:
  empty_xclb s = !cid p st.
  FLOOKUP s cid = SOME $ Core cid p st
  ==> st.bst_xclb = NONE
End

(* enforce restriction on core id *)

Definition wf_trace1_def:
  wf_trace1 tr =
    !i cid cid' p st. i < LENGTH tr
      /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid' p st
      ==> cid = cid'
End

Theorem wf_trace1_FLOOKUP:
  !tr i id x. wf_trace1 tr
  /\ FLOOKUP (FST $ EL i tr) id = SOME x
  /\ i < LENGTH tr
  ==> ?p st. x = Core id p st
Proof
  rw[wf_trace1_def]
  >> qmatch_assum_rename_tac `FLOOKUP _ _ = SOME x`
  >> Cases_on `x`
  >> res_tac
  >> fs[]
QED


(* well-formed traces are certified and thread id's are unique identifiers *)
Definition wf_trace_def:
  wf_trace tr <=> tr IN par_traces
    /\ NULL $ SND $ HD tr /\ empty_prom $ FST $ HD tr
    /\ empty_xclb $ FST $ HD tr
End

Theorem wf_trace_NOT_NULL:
  !tr. wf_trace tr ==> ~NULL tr
Proof
  rw[wf_trace_def,par_traces_def,gen_traces_def]
  >> imp_res_tac is_gen_trace_NOT_NULL
QED

Theorem wf_trace_parstep_EL:
  !tr i. wf_trace tr /\ SUC i < LENGTH tr
  ==> ?cid. parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rw[wf_trace_def,par_traces_def,gen_traces_def]
  >> drule is_gen_trace_EL
  >> fs[]
QED

Theorem wf_trace_LENGTH_SND:
  !tr i. wf_trace tr /\ SUC i < LENGTH tr
  ==> LENGTH (SND $ EL i tr) <= LENGTH (SND $ EL (SUC i) tr)
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> imp_res_tac parstep_nice_memory_imp
  >> fs[]
QED

Theorem wf_trace_LENGTH_SND':
  !tr i j. wf_trace tr /\ i + j < LENGTH tr
  ==> LENGTH (SND $ EL i tr) <= LENGTH (SND $ EL (i + j) tr)
Proof
  ntac 2 gen_tac >> Induct >> rw[]
  >> fs[]
  >> dxrule_then irule LESS_EQ_TRANS
  >> `i + SUC j = SUC $ i + j` by fs[]
  >> pop_assum $ fs o single
  >> irule wf_trace_LENGTH_SND
  >> fs[]
QED

(* memory is less or equal to trace length *)

Theorem wf_trace_LENGTH_SND'':
  !tr i cid. wf_trace tr /\ i < LENGTH tr
  ==> LENGTH $ SND $ EL i tr <= i
Proof
  gen_tac >> Induct
  >- fs[wf_trace_def,NULL_EQ]
  >> rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> dxrule_then strip_assume_tac parstep_nice_memory_imp
  >> fs[]
QED

(* if a core writes to memory there is the corresponding parstep transition *)

Theorem wf_trace_adds_to_memory:
  !i tr k cid. wf_trace tr /\ i < LENGTH tr
  /\ k < LENGTH $ SND $ EL i tr
  /\ (EL k $ SND $ EL i tr).cid = cid
  ==> ?j. j < i /\ parstep_nice cid (EL j tr) (EL (SUC j) tr)
    /\ k = LENGTH $ SND $ EL j tr
    /\ SUC k = LENGTH $ SND $ EL (SUC j) tr
Proof
  Induct >> rw[DISJ_EQ_IMP]
  >- fs[wf_trace_def,NULL_EQ,NOT_LESS]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> imp_res_tac parstep_nice_memory_imp
  >- (
    first_x_assum drule
    >> fs[]
    >> disch_then $ drule_then strip_assume_tac
    >> rpt $ goal_assum $ drule_at Any
    >> fs[]
  )
  >> gvs[prim_recTheory.LESS_THM,GSYM ADD1,EL_APPEND2]
  >> dsimp[]
  >> first_x_assum drule
  >> fs[]
  >> disch_then $ drule_then strip_assume_tac
  >> rpt $ goal_assum $ drule_at Any
  >> fs[EL_APPEND1]
QED

(* same core id occurs in next step in the trace *)

Theorem wf_trace_cid_forward1:
  !tr i cid p st. wf_trace tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ SUC i < LENGTH tr
  ==> ?st. FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all_then irule parstep_nice_FLOOKUP
QED

(* same core id occurs later in the trace *)

Theorem wf_trace_cid_forward:
  !j tr i cid p st. wf_trace tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ i <= j /\ j < LENGTH tr
  ==> ?st. FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
Proof
  Induct >> rw[] >> fs[]
  >> dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >- (
    first_x_assum $ drule_then dxrule
    >> rw[]
    >> drule_then irule wf_trace_cid_forward1
    >> rpt $ goal_assum $ drule_at Any
  )
  >> gvs[] >> goal_assum drule
QED

(* same core id occurs earlier in the trace *)

Theorem wf_trace_cid_backward1:
  !i tr cid p st. wf_trace tr
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st
  /\ SUC i < LENGTH tr
  ==> ?st. FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
Proof
  rpt strip_tac
  >> drule_all wf_trace_parstep_EL
  >> disch_then $ qx_choose_then `cid'` assume_tac
  >> Cases_on `cid = cid'`
  >> gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
QED

Theorem wf_trace_cid_backward:
  !i j tr cid p st. wf_trace tr
  /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
  /\ i <= j /\ j < LENGTH tr
  ==> ?st. FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
Proof
  ntac 2 gen_tac >> Induct_on `j - i`
  >> rw[] >> fs[PULL_FORALL,AND_IMP_INTRO]
  >- gvs[LESS_OR_EQ]
  >> drule_then irule wf_trace_cid_backward1
  >> qpat_x_assum `_ = _ - _:num` $ assume_tac o REWRITE_RULE[SUB_LEFT_EQ]
  >> gvs[]
  >> first_x_assum $ rev_drule_at_then Any irule
  >> goal_assum $ rev_drule_at Any
  >> fs[]
QED

(* a core id occurs in all states *)

Theorem wf_trace_cid:
  !tr cid p st i j. wf_trace tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ i < LENGTH tr /\ j < LENGTH tr
  ==> ?st. FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
Proof
  rw[]
  >> Cases_on `i <= j`
  >- (
    drule_then irule wf_trace_cid_forward
    >> rpt $ goal_assum $ drule_at Any
  )
  >> drule_then irule wf_trace_cid_backward
  >> goal_assum $ rev_drule_at Any
  >> fs[]
QED

(* bst_prom are no larger than memory length *)

Theorem wf_trace_EVERY_LENGTH_bst_prom_inv:
  !i tr cid p st.
  wf_trace tr /\ i < LENGTH tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> EVERY (λx. 0 < x /\ x <= LENGTH $ SND $ EL i tr) st.bst_prom
Proof
  Induct
  >- (
    rw[wf_trace_def,empty_prom_def]
    >> res_tac >> fs[NULL_EQ]
  )
  >> rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> first_x_assum $ drule_then $ drule_at Any
  >> Cases_on `cid = cid'`
  >> gvs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE]
  >> imp_res_tac clstep_EVERY_LENGTH_bst_prom_inv
  >> gvs[]
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

(* memory only ever increases *)

Theorem wf_trace_IS_PREFIX_SND_EL':
  !tr i j. wf_trace tr /\ i <= j /\ j < LENGTH tr
  ==> IS_PREFIX (SND $ EL j tr) (SND $ EL i tr)
Proof
  rpt gen_tac
  >> Induct_on `j - i`
  >> rw[SUB_LEFT_EQ] >> fs[PULL_FORALL,AND_IMP_INTRO]
  >- (
    dxrule_all_then assume_tac $ iffLR $ GSYM EQ_LESS_EQ
    >> fs[]
  )
  >> `i + SUC v = SUC $ i + v` by fs[]
  >> pop_assum $ fs o single
  >> first_x_assum $ qspecl_then [`v+i`,`i`] assume_tac
  >> `i + v < LENGTH tr` by fs[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> imp_res_tac parstep_nice_memory_imp
  >> Cases_on `v=0`
  >> gvs[]
  >> fs[IS_PREFIX_APPEND]
QED

Theorem wf_trace_IS_PREFIX_SND_EL =
  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [LESS_OR_EQ] wf_trace_IS_PREFIX_SND_EL'

Theorem wf_trace_memory_LENGTH:
  !tr i j. wf_trace tr /\ i <= j /\ j < LENGTH tr
  ==> LENGTH (SND $ EL i tr) <= LENGTH (SND $ EL j tr)
Proof
  rpt strip_tac
  >> drule_all wf_trace_IS_PREFIX_SND_EL'
  >> fs[IS_PREFIX_LENGTH]
QED

Theorem wf_trace_EL_SND_EQ_EL_SND:
  !tr i j k. wf_trace tr /\ i < LENGTH tr /\ j < LENGTH tr
  /\ k < LENGTH $ SND $ EL i tr /\ k < LENGTH $ SND $ EL j tr
  ==> EL k (SND $ EL j tr) = EL k (SND $ EL i tr)
Proof
  rpt strip_tac
  >> Cases_on `i < j`
  >> gs[NOT_LESS,LESS_OR_EQ]
  >> drule_at_then Any drule wf_trace_IS_PREFIX_SND_EL
  >> strip_tac
  >> gs[IS_PREFIX_APPEND,EL_APPEND1]
QED

(* only one core changes in a transition *)

Theorem wf_trace_unchanged:
  !tr p1 p1' p2 p2' cid cid' st1 st1' st2 st2' i.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p1 st1
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p1 st1'
  /\ FLOOKUP (FST $ EL i tr) cid' = SOME $ Core cid' p2 st2
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid' = SOME $ Core cid' p2' st2'
  /\ cid <> cid' /\ st1 <> st1'
  ==> p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then assume_tac wf_trace_parstep_EL
  >> gvs[parstep_cases,parstep_nice_def,FLOOKUP_UPDATE]
  >> Cases_on `cid' = cid''`
  >> gvs[]
QED

(* identify the progressing core *)

Theorem wf_trace_cid_NOT_EQ:
  !tr cid i cid' p st st'.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid' = SOME $ Core cid' p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid' = SOME $ Core cid' p st'
  /\ cid <> cid'
  ==> st = st'
Proof
  rpt strip_tac
  >> gvs[parstep_cases,parstep_nice_def,FLOOKUP_UPDATE]
QED

Triviality wf_trace_parstep_nice_NOT_parstep_nice:
  !tr i cid cid'. wf_trace tr /\ SUC i < LENGTH tr
  /\ ~parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid <> cid'
Proof
  rpt strip_tac >> gvs[]
QED

Theorem wf_trace_NOT_parstep_nice_state_EQ':
  !tr i cid p st st'. wf_trace tr /\ SUC i < LENGTH tr
  /\ ~parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> st = st'
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> drule wf_trace_parstep_nice_NOT_parstep_nice
  >> rpt $ disch_then drule
  >> drule wf_trace_cid_NOT_EQ
  >> rpt $ disch_then drule
  >> fs[]
QED

Theorem wf_trace_NOT_parstep_nice_state_EQ:
  !j k tr cid p st st'. wf_trace tr
  /\ j <= k /\ k < LENGTH tr
  /\ (!i. j <= i /\ i < k /\ SUC i < LENGTH tr
    ==> ~parstep_nice cid (EL i tr) (EL (SUC i) tr))
  /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL k tr) cid = SOME $ Core cid p st'
  ==> st = st'
Proof
  ntac 2 gen_tac
  >> Induct_on `k - j`
  >- (
    dsimp[LESS_OR_EQ]
    >> rw[]
    >> fs[]
  )
  >> rw[SUB_LEFT_EQ]
  >> `j + SUC v = SUC $ j + v` by fs[]
  >> pop_assum $ fs o single
  >> `?st''. FLOOKUP (FST $ EL (j + v) tr) cid = SOME $ Core cid p st'' ` by (
    drule_at_then Any assume_tac wf_trace_cid_backward1
    >> gs[]
  )
  >> drule_at Any wf_trace_NOT_parstep_nice_state_EQ'
  >> disch_then $ dxrule_at Any
  >> rw[]
  >> last_x_assum irule
  >> rpt $ goal_assum $ drule_at Any
  >> fs[]
QED

(* certified traces have empty promises in the last state *)

Theorem wf_trace_LAST_NULL_bst_prom:
  !tr cid p st. wf_trace tr
  /\ FLOOKUP (FST $ LAST tr) cid = SOME $ Core cid p st
  ==> NULL st.bst_prom
Proof
  rpt strip_tac
  >> imp_res_tac wf_trace_NOT_NULL
  >> Cases_on `LENGTH tr = 1`
  >- (
    gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL,wf_trace_def,empty_prom_def]
    >> res_tac
  )
  >> spose_not_then assume_tac
  >> gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL,NOT_NUM_EQ]
  >> qabbrev_tac `P = λj. 1 < j /\ j <= LENGTH tr /\ parstep_nice cid (EL (LENGTH tr - j) tr) (EL (SUC $ LENGTH tr - j) tr)`
  >> Cases_on `?i. P i`
  >- (
    dxrule_then assume_tac arithmeticTheory.WOP
    >> fs[Abbr`P`,DISJ_EQ_IMP,AND_IMP_INTRO]
    >> qmatch_assum_abbrev_tac `parstep_nice _ _ (EL j _)`
    >> `j < LENGTH tr` by fs[Abbr`j`]
    >> `FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st` by (
      drule_then (drule_then $ qspec_then `j` assume_tac) wf_trace_cid_backward
      >> gs[]
      >> dxrule_then assume_tac $ iffLR LESS_EQ
      >> reverse $ dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
      >- (
        `j = PRE $ LENGTH tr` by fs[]
        >> pop_assum $ fs o single
      )
      >> drule_then (rev_drule_at $ Pos last) wf_trace_NOT_parstep_nice_state_EQ
      >> disch_then $ drule_at $ Pos last
      >> impl_tac
      >- (
        rw[]
        >> first_x_assum $ qspec_then `LENGTH tr - i` mp_tac
        >> fs[Abbr`j`]
      )
      >> rw[] >> fs[]
    )
    >> PRED_ASSUM is_forall kall_tac
    >> `is_certified p cid st (SND (EL j tr))` by (
      gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
    )
    >> fs[is_certified_def]
    >> drule_then assume_tac cstep_seq_rtc_bst_prom_EQ
    >> qmatch_assum_abbrev_tac `A ==> _ /\ _`
    >> `A` by (
      fs[Abbr`A`]
      >> drule_then irule wf_trace_EVERY_LENGTH_bst_prom_inv
      >> dsimp[]
      >> goal_assum drule
    )
    >> gvs[]
  )
  >> drule_then (drule_then $ qspec_then `0` assume_tac) wf_trace_cid_backward
  >> gs[Excl"EL",GSYM EL,Excl"EL_restricted"]
  >> drule_then (drule_at Any) wf_trace_NOT_parstep_nice_state_EQ
  >> disch_then $ rev_drule_at Any
  >> impl_tac
  >- (
    rw[]
    >> first_x_assum $ qspec_then `LENGTH tr - i` mp_tac
    >> fs[Abbr`P`,DISJ_EQ_IMP]
  )
  >> disch_then $ fs o single
  >> fs[wf_trace_def,empty_prom_def,LENGTH_NOT_NULL]
  >> res_tac
QED

(* new later promises are strictly larger than memory length *)

Theorem wf_trace_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom:
  !i j tr cid p st st'. wf_trace tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ i < j /\ j < LENGTH tr
  /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st'
  ==> EVERY (λx. ~MEM x st.bst_prom ==> LENGTH (SND $ EL i tr) < x) st'.bst_prom
Proof
  ntac 2 gen_tac
  >> Induct_on `j - i`
  >> rw[SUB_LEFT_EQ]
  >> qmatch_asmsub_rename_tac `SUC v`
  >> Cases_on `v = 0`
  >- (
    fs[GSYM ADD1]
    >> drule_all_then strip_assume_tac wf_trace_parstep_EL
    >> Cases_on `cid = cid'`
    >- (
      dxrule_then assume_tac parstep_nice_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom
      >> fs[]
    )
    >> drule_then (rev_drule_then assume_tac) parstep_nice_FLOOKUP'
    >> gvs[EVERY_MEM]
  )
  >> `i + SUC v = SUC $ i + v` by fs[]
  >> pop_assum $ fs o single
  >> drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[AND_IMP_INTRO,PULL_FORALL,SUB_LEFT_EQ]
  >> first_x_assum $ drule_at_then (Pos $ el 4) assume_tac
  >> gs[]
  >> Cases_on `cid = cid'`
  >- (
    drule_then assume_tac parstep_nice_EVERY_NOT_MEM_bst_prom_LENGTH_LESS_bst_prom
    >> gvs[EVERY_MEM,AND_IMP_INTRO]
    >> rw[]
    >> ntac 2 $ first_x_assum $ drule_at_then Any assume_tac
    >> qmatch_assum_abbrev_tac `A ==> LENGTH _ < _`
    >> Cases_on `A`
    >> fs[]
    >> dxrule_at_then Any irule LESS_EQ_LESS_TRANS
    >> irule wf_trace_LENGTH_SND'
    >> fs[]
  )
  >> drule_then (rev_drule_then assume_tac) parstep_nice_FLOOKUP'
  >> gvs[]
QED

val _ = export_theory();
