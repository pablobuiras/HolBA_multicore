
open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory spinlockAbstractTheory spinlockConcreteTheory;

val _ = new_theory "spinlockRefinement";

(* TODO define statement *)
Definition same_pc_als_slf_def:
  same_pc_als_slf pc pc' <=>
(* manually match pcs in lock and unlock region *)
(*
  for abstract and concrete pc, project
    (b,n) ∈ block x statement
  into :num as
    sum [i < b. blockwidth i]  + n
  and equate (assuming the offset is accounted for)
*)
    (ARB :bool)
End

(* the spinlock refinement relation between abstract state aS
 * and concrete state S for a core id cid *)
(* TODO parametrise over projection of aS and S at cid *)
Definition asl_slf_rel_def:
  asl_slf_rel cid aS S =
  (!cores M acores aM agenv genv apc pc lbl index albl aindex.
       cores = FST S
    /\ M = FST $ SND S
    /\ genv = SND $ SND S
    /\ pc = core_pc cid S
    /\ lbl = core_pc_lbl cid S
    /\ index = core_pc_index cid S
    /\ acores = FST aS
    /\ aM = FST $ SND aS
    /\ agenv = SND $ SND aS
    /\ apc = core_pc cid aS
    /\ albl = core_pc_lbl cid aS
    /\ aindex = core_pc_index cid aS
    ==>
    (* we only reason about reachable states *)
       reachable_asl apc
    /\ reachable_slf pc
    /\ core_prog cid aS = spinlock_aprog cid
    /\ core_prog cid S = (bir_spinlockfull_prog: string bir_program_t)
    (* lock is free *)
    /\ is_free_slf cid S = is_free_asl agenv
    (* pc outside lock and unlock *)
    /\ (
      outside_un_lock_asl apc
      /\ outside_un_lock_slf pc
      ==> same_pc_als_slf apc pc
(*
spinlock_aprog_def
bir_spinlockfull_prog_def
*)
    )
    (* not taking the lock *)
    /\ (
      (lbl < 20w
      /\ (lbl = 20w ==>
          bir_read_core_reg_zero "x6" cid S) (* unsuccessful store *)
      ) ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 0w,0)
    )
    (* future successful store *)
    /\ (
        lbl = 20w
        /\ ~bir_read_core_reg_zero "x6" cid S
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* successful store *)
    /\ (
        lbl = 24w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after lock, before unlock *)
    /\ (
        24w < lbl /\ lbl < 40w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
        lbl = 40w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 8w,0)
    )
  )
End


(*****************************************************************************)
(* The refinemen theorem(s) **************************************************)
(*****************************************************************************)

Theorem bir_spinlockfull_prog_not_is_xcl_write:
  pc.bpc_label = BL_Address (Imm64 36w)
  /\ pc.bpc_index = 2
  ==> ~is_xcl_write bir_spinlockfull_prog pc
Proof
  rpt gen_tac >> strip_tac
  >> EVAL_TAC
  >> fs[]
QED

Theorem bir_spinlockfull_prog_is_xcl_write:
  pc.bpc_label = BL_Address (Imm64 16w)
  /\ pc.bpc_index = 2
  ==> is_xcl_write bir_spinlockfull_prog pc
Proof
  rpt strip_tac
  >> EVAL_TAC
  >> fs[]
QED

Theorem bir_spinlockfull_prog_is_xcl_read:
  pc.bpc_label = BL_Address (Imm64 4w)
  /\ pc.bpc_index = 1
  ==> is_xcl_read bir_spinlockfull_prog pc
    $ BExp_Den $ BVar "x7" $ BType_Imm Bit64
Proof
  rpt strip_tac
  >> EVAL_TAC
  >> fs[]
QED

(* read transitions *)
Theorem spinlock_refinement_Read:
  !cid tr i aS st var a_e opt_cast xcl acq rel.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid (bir_spinlockfull_prog :string bir_program_t) st)
  /\ FLOOKUP (FST aS) cid = SOME $ Core cid (spinlock_aprog cid) st'
  /\ bir_get_stmt (bir_spinlockfull_prog :string bir_program_t) st.bst_pc =
        BirStmt_Read var a_e opt_cast xcl acq rel
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> disj1_tac
  >> drule_then strip_assume_tac $ iffLR bir_get_stmt_bir_spinlockfull_prog_BirStmt_Read
  >> dxrule_then assume_tac $ iffLR parstep_nice_def
  >> gs[parstep_cases,cstep_cases,clstep_cases,get_core_state_def,FLOOKUP_UPDATE,core_zoo,asl_slf_rel_def,bir_spinlockfull_prog_is_xcl_read,bir_programTheory.bir_pc_next_def,get_core_prog_def]
  >> conj_tac
  >- simp[reachable_slf_def,bst_pc_tuple_def]
  >> conj_tac
  >- (
    qmatch_goalsub_abbrev_tac `_ = B`
    >> qpat_x_assum `_ = B` $ fs o single o GSYM
    >> fs[is_free_slf_def,core_zoo,bir_read_mem_var_def,FLOOKUP_UPDATE]
    (* MEM8.x7 holds the default 0w before and after reading from *)
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` mp_tac
    >> fs[bir_eval_exp_view_def,bir_eval_exp_mix_def,is_global_def]
    >> fs[]
    >> cheat
  )
  >> cheat
QED

(* write transitions *)
Theorem spinlock_refinement_Write:
  !cid tr i aS st a_e v_e xcl acq rel.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt bir_spinlockfull_prog st.bst_pc =
    BirStmt_Write a_e v_e xcl acq rel
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* generic transitions *)
Theorem spinlock_refinement_Generic:
  !cid tr i aS st stm.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt bir_spinlockfull_prog st.bst_pc = BirStmt_Generic stm
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* fence transitions *)
Theorem spinlock_refinement_Fence:
  !cid tr i aS st mo1 mo2.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt (bir_spinlockfull_prog :string bir_program_t) st.bst_pc = BirStmt_Fence mo1 mo2
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* expr transitions *)
Theorem spinlock_refinement_Expr:
  !cid tr i aS st var e.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt bir_spinlockfull_prog st.bst_pc = BirStmt_Expr var e
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* branch transitions *)
Theorem spinlock_refinement_Branch:
  !cid tr i aS st a1 a2 a3.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt bir_spinlockfull_prog st.bst_pc = BirStmt_Branch a1 a2 a3
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* amo transitions *)
(* TODO no amo instructions;
   solved by evaluating bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo *)
Theorem spinlock_refinement_Amo:
  !cid tr i aS st var a_e v_e acq rel.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid bir_spinlockfull_prog st)
  /\ bir_get_stmt bir_spinlockfull_prog st.bst_pc =
    BirStmt_Amo var a_e v_e acq rel
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
QED

(* refinement theorem *)
(* the abstract state is prefixed with "a" *)

Theorem spinlock_refinement:
  !cid tr i aS.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  ==>
    asl_slf_rel cid aS (EL (SUC i) tr)
    \/ ?aS'. parstep_nice cid aS aS'
          /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_then assume_tac $ iffLR asl_slf_rel_def
  >> gs[]
  >> reverse $ drule_then strip_assume_tac parstep_nice_memory_imp
  (* promise case *)
  >- (
    disj1_tac
    >> cheat (* no relevant change of state *)
  )
  >> qmatch_asmsub_rename_tac `asl_slf_rel cid aS' _`
  >> `?st st' ast.
    FLOOKUP (FST (EL i tr)) cid = SOME (Core cid (bir_spinlockfull_prog :string bir_program_t) st)
    /\ FLOOKUP (FST (EL (SUC i) tr)) cid = SOME (Core cid (bir_spinlockfull_prog :string bir_program_t) st')
    /\ FLOOKUP (FST aS') cid = SOME (Core cid (spinlock_aprog cid) ast)
  ` by (
    cheat
  )
  >> gvs[core_pc_def,core_state_def,get_core_state_def,core_def,parstep_nice_def,bst_pc_tuple_def,core_pc_lbl_def,core_pc_index_def,addr_val_def]
  >> drule_then strip_assume_tac $ iffLR parstep_cases
  >> gs[clstep_cases,cstep_cases]
  (* 8 goals *)
  >~ [`bir_get_stmt _ _ = BirStmt_Write a_e v_e xcl acq rel`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Write
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Write a_e v_e xcl acq rel`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Write
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Read var a_e opt_cast xcl acq rel`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Read
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Fence mo1 mo2`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Fence
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Generic stm`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Generic
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Branch a1 a2 a3`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Branch
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Amo var a_e v_e acq rel`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Amo
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
  >~ [`bir_get_stmt _ _ = BirStmt_Expr var e`]
  >- (
    drule_at (Pat `bir_get_stmt _ _ = _`) spinlock_refinement_Expr
    >> rpt $ disch_then $ drule_at Any
    >> fs[parstep_nice_def]
  )
QED

(*
reachability for free for traces
*)

val _ = export_theory();

