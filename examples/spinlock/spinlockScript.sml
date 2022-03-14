open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;
open bir_promisingTheory rich_listTheory listTheory arithmeticTheory tracesTheory;
open finite_mapTheory tracestepTheory;

(*
 * correctness of spinlock.da (backwards reasoning) 
 *)

val _ = new_theory "spinlock";

(* lift the program *)

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val (bir_spinlock_progbin_def, bir_spinlock_prog_def, bir_is_lifted_prog_spinlock) = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));


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
    /\ st = bir_state_init prog
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
  !pc var a_e opt_cast xcl acq rel.
  bir_get_stmt (bir_spinlock_prog:'a bir_program_t) pc
  = BirStmt_Read var a_e opt_cast xcl acq rel
  <=> pc = <| bpc_index := 1; bpc_label := BL_Address $ Imm64 12w|>
    /\ var = BVar "x5" $ BType_Imm Bit64
    /\ opt_cast = SOME (BIExp_SignedCast,Bit64)
    /\ a_e = BExp_Den spinlock_var
    /\ xcl
    /\ acq = is_acq (bir_spinlock_prog:'a bir_program_t) pc
    /\ rel = is_rel (bir_spinlock_prog:'a bir_program_t) pc
Proof
  fs[Once EQ_IMP_THM]
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
  !pc a_e v_e xcl acq rel.
  bir_get_stmt (bir_spinlock_prog:'a bir_program_t) pc
  = BirStmt_Write a_e v_e xcl acq rel
  <=> (
    pc = <| bpc_index := 2; bpc_label := BL_Address $ Imm64 12w|>
    /\ a_e = BExp_Den spinlock_var
    /\ v_e = BExp_Const (Imm32 0x1010101w)
    /\ ~xcl
    /\ acq = is_acq (bir_spinlock_prog:'a bir_program_t) pc
    /\ rel = is_rel (bir_spinlock_prog:'a bir_program_t) pc
  ) \/ (
    pc = <| bpc_index := 2; bpc_label := BL_Address $ Imm64 20w|>
    /\ a_e = BExp_Den spinlock_var
    /\ v_e = BExp_Cast BIExp_LowCast (BExp_Den $ BVar "x0" $ BType_Imm Bit64) Bit32
    /\ xcl
    /\ acq = is_acq (bir_spinlock_prog:'a bir_program_t) pc
    /\ rel = is_rel (bir_spinlock_prog:'a bir_program_t) pc
  )
Proof
  fs[Once EQ_IMP_THM]
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
    = SOME $ (EL (PRE t) $ SND $ EL (SUC i) tr).loc
    /\ ?v. (EL (PRE t) $ SND $ EL (SUC i) tr).val = BVal_Imm v
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then assume_tac is_fulfil_xcl_is_fulfil
  >> dxrule_at_then (Pat `is_fulfil _ _ _`) assume_tac is_fulfil_parstep_nice_eq
  >> drule_at Any wf_trace_core_runs_spinlock_FLOOKUP
  >> disch_then $ drule_at_then Any assume_tac
  >> gvs[is_fulfil_xcl_def,FLOOKUP_UPDATE,bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ]
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
  >> fs[bir_envTheory.bir_env_default_def,varset_of_spinlock_prog,bir_envTheory.bir_envty_of_vs_def,bir_programTheory.bir_state_init_def]
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
  >> qmatch_assum_rename_tac `fulfil_atomic_ok (SND $ EL (SUC i') tr) _ cid' _ t'`
  >> qmatch_assum_rename_tac `fulfil_atomic_ok (SND $ EL (SUC i) tr) _ cid _ t`
  >> `(EL (PRE t) (SND $ EL (SUC i) tr)).loc = k /\ (EL (PRE t') (SND $ EL (SUC i') tr)).loc = k` by (
    ntac 2 $ dxrule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_to_memory
    >> drule cores_run_spinlock_unique_loc
    >> disch_then $ (fn x =>
      qspecl_then [`k`,`SUC i'`,`EL (PRE t') $ SND $ EL (SUC i') tr`] assume_tac x
      >> qspecl_then [`k`,`SUC i`,`EL (PRE t) $ SND $ EL (SUC i) tr`] assume_tac x
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
