
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
(*
spinlock_aprog_def
bir_spinlockfull_prog_def
*)
    (* not taking the lock *)
    /\ (
      lbl < 20w
      /\ (lbl = 16w /\ index = 5 ==>
          bir_read_core_reg_zero "x6" cid S) (* unsuccessful store *)
      ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 0w,0)
    )
    (* future successful store *)
    /\ (
      lbl = 16w
      /\ ~bir_read_core_reg_zero "x6" cid S
      ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after lock, before unlock *)
    /\ (
      24w <= lbl /\ lbl <= 36w /\ (lbl = 36w ==> index = 2)
      ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
      36w <= lbl /\ (lbl = 36w ==> 3 <= index)
      ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,1)
    )
    /\ atomicity_ok cid (FST aS)
    /\ is_certified (core_prog cid aS) cid (core_state cid aS) aM agenv
  )
End

(*****************************************************************************)
(* Properties about spinlock programs ****************************************)
(*****************************************************************************)

Theorem bir_spinlockfull_prog_write_props36w:
  pc.bpc_label = BL_Address (Imm64 36w)
  /\ pc.bpc_index = 2
  ==> ~is_xcl_write bir_spinlockfull_prog pc
    /\ ~is_amo bir_spinlockfull_prog pc
    /\ ~is_acq bir_spinlockfull_prog pc
    /\ ~is_rel bir_spinlockfull_prog pc
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

Theorem bir_spinlock_aprog_not_is_amo_is_xcl_write:
  pc.bpc_label = BL_Address (Imm64 4w)
  /\ pc.bpc_index = 0
  ==> ~is_amo (spinlock_aprog cid) pc
    /\ ~is_xcl_write (spinlock_aprog cid) pc
    /\ ~is_rel (spinlock_aprog cid) pc
    /\ ~is_acq (spinlock_aprog cid) pc
Proof
  rpt gen_tac >> strip_tac
  >> EVAL_TAC
  >> fs[]
QED

(* TODO adjust prerequisites for spinlock_refinement_Read *)
Theorem env_update_cast64_thm:
  !env new_env var x i v genv genv' mem.
  env_update_cast64 (BVar var i) (BVal_Imm v) env genv = SOME (new_env,genv')
  /\ var <> x
  ==> bir_read_mem_var mem x new_env
    = bir_read_mem_var mem x env
Proof
  Cases >> rw[env_update_cast64_def]
  >> EVAL_TAC
  >> BasicProvers.every_case_tac
  >> fs[pairTheory.ELIM_UNCURRY,bir_envTheory.bir_env_update_def,bir_expTheory.bir_eval_load_def,bir_envTheory.bir_var_name_def]
  >> rpt (
    qmatch_asmsub_rename_tac `type_of_bir_val z`
    >> Cases_on `z` >> fs[bir_valuesTheory.type_of_bir_val_def]
  )
  >> gvs[bir_expTheory.bir_eval_load_def,AllCaseEqs(),bir_envTheory.bir_env_lookup_def]
  >> rpt (
    qmatch_asmsub_rename_tac `type_of_bir_imm b`
    >> Cases_on `b` >> fs[bir_immTheory.type_of_bir_imm_def]
  )
  >> fs[]
  >> cheat (* TODO *)
QED

(* for memories obtained during parstep transitions *)
(* TODO adjust prerequisites for spinlock_refinement_Read *)
Theorem parstep_nice_mem_read_BVal_Imm:
  mem_read M l t = SOME x ==> ?y. x = BVal_Imm y
Proof
  cheat
QED

Definition parsteps_def:
  parsteps cid sys1 sys2 <=> ?n. NRC (λsys1 sys2. parstep_nice cid sys1 sys2) n sys1 sys2 
End

(*****************************************************************************)
(* The refinemen theorem(s) **************************************************)
(*****************************************************************************)

(* read transitions *)
Theorem spinlock_refinement_Read:
  !cid tr i aS st var a_e opt_cast xcl acq rel st'.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid (bir_spinlockfull_prog :string bir_program_t) st)
  /\ FLOOKUP (FST aS) cid = SOME $ Core cid (spinlock_aprog cid) st'
  /\ bir_get_stmt (bir_spinlockfull_prog :string bir_program_t) st.bst_pc =
        BirStmt_Read var a_e opt_cast xcl acq rel
  /\ FST (SND (EL i tr)) = FST (SND (EL (SUC i) tr))
  ==>
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> fs[parsteps_def,PULL_EXISTS]
  >> irule_at Any $ iffRL NRC_0
  >> drule_then strip_assume_tac $ iffLR bir_get_stmt_bir_spinlockfull_prog_BirStmt_Read
  >> dxrule_then assume_tac $ iffLR parstep_nice_def
  >> gs[parstep_cases,cstep_cases,clstep_cases,get_core_state_def,FLOOKUP_UPDATE,core_zoo,asl_slf_rel_def,bir_spinlockfull_prog_is_xcl_read,bir_programTheory.bir_pc_next_def,get_core_prog_def]
  >> conj_tac
  >- simp[reachable_slf_def,bst_pc_tuple_def]
  >- (
    qpat_x_assum `is_free_slf _ _ <=> _` $ REWRITE_TAC o single o GSYM
    >> fs[is_free_slf_def,is_free_asl_def,core_zoo,get_core_state_def,FLOOKUP_UPDATE]
    >> qmatch_asmsub_rename_tac `env_update_cast64 _ v _ _`
    >> imp_res_tac parstep_nice_mem_read_BVal_Imm
    >> gvs[]
    >> drule_at Any $ GSYM env_update_cast64_thm
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac $ iffLR bir_get_stmt_bir_spinlockfull_prog_BirStmt_Write
  (*
  >> dxrule_then assume_tac $ iffLR parstep_nice_def
  >> gs[parstep_cases,cstep_cases,clstep_cases,get_core_state_def,FLOOKUP_UPDATE,core_zoo,bir_spinlockfull_prog_write_props36w,bir_programTheory.bir_pc_next_def,get_core_prog_def]
  *)
  >- (
    (* 36w, 2: leaving lock section *)
    `FLOOKUP (FST aS') cid = SOME $ Core cid (spinlock_aprog cid) st'` by (
      cheat
    )
    >> `bst_pc_tuple $ core_pc cid aS' = (BL_Address $ Imm64 4w,0)` by (
      fs[core_zoo,asl_slf_rel_def]
    )
    >> dsimp[parstep_nice_def,parstep_cases,cstep_cases,pairTheory.EXISTS_PROD]
    >> fs[bst_pc_tuple_def,GSYM PULL_EXISTS,AC CONJ_ASSOC CONJ_COMM]
    (*
    >> conj_tac
    >- fs[atomicity_ok_def,asl_slf_rel_def]
    *)
    >> `?a_e v_e xcl acq rel.
      bir_get_stmt (spinlock_aprog cid) (core_pc cid aS')
      = BirStmt_Write a_e v_e xcl acq rel` by (
      fs[bir_get_stmt_spinlock_aprog_BirStmt_Write,bir_spinlock_aprog_not_is_amo_is_xcl_write]
    )
    >> dsimp[clstep_cases,FLOOKUP_UPDATE]
    >> gs[core_zoo,get_core_state_def]
    >> drule_then assume_tac $ iffLR bir_get_stmt_spinlock_aprog_BirStmt_Write
    >> gs[core_zoo,bir_spinlock_aprog_not_is_amo_is_xcl_write,bir_spinlockfull_prog_write_props36w]
    >> cheat
  )
  >- (
    (* 16w 2 *)
    (* case split on success of write *)
    Cases_on `bir_read_core_reg_zero "x6" cid (EL (SUC i) tr)`
    >- (
      (* unsuccessful *)
      cheat
    )
    (* successful *)
    >> cheat
  )
  >- (
    (* 4w 2 *)
    drule_then assume_tac $ iffLR asl_slf_rel_def
    >> gs[reachable_slf_def,core_zoo]
  )
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> `reachable_slf (core_pc cid (EL i tr))` by fs[asl_slf_rel_def]
  >> drule_then strip_assume_tac $ iffLR bir_get_stmt_bir_spinlockfull_prog_BirStmt_Generic
  >> gs[reachable_slf_def,core_zoo]
  >- (
    (* 0w,1 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 4w,0 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 4w,3 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 12w,1 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 16w,0 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 16w,1 *)
    (* in lock *)
    cheat
  )
  >- (
    (* 16w,5 *)
    (* in crit *)
    cheat
  )
  >- (
    (* 24w,0 *)
    (* in crit *)
    cheat
  )
  >- (
    (* 28w,1 *)
    (* in crit *)
    cheat
  )
  >- (
    (* 32w,1 *)
    (* in unlock - after fence *)
    cheat
  )
  >- (
    (* 36w,1 *)
    (* in unlock - after fence *)
    cheat
  )
  >- (
    (* 36w,0 *)
    (* in unlock - after fence *)
    cheat
  )
  >- (
    (* 36w,3 *)
    (* leaving unlock *)
    cheat
  )
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
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
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  cheat
(* bir_get_stmt_spinlock_aprog_BirStmt_Amo, bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo *)
QED

(* refinement theorem *)
(* the abstract state is prefixed with "a" *)

(* TODO change to parstep_nice^* *)
Theorem spinlock_refinement:
  !cid tr i aS.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ asl_slf_rel cid aS (EL i tr)
  ==>
    ?aS'. parsteps cid aS aS' /\ asl_slf_rel cid aS' (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_then assume_tac $ iffLR asl_slf_rel_def
  >> gs[]
  >> reverse $ drule_then strip_assume_tac parstep_nice_memory_imp
  (* promise case *)
  >- (
    fs[parsteps_def,PULL_EXISTS]
    >> irule_at Any $ iffRL NRC_0
    >> fs[]
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

val _ = export_theory();

