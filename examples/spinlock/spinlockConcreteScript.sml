
open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory
(* tracestepTheory spinlockTheory ; *)

val _ = new_theory "spinlockConcrete";

(*****************************************************************************)
(* The full spinlock program *************************************************)
(*****************************************************************************)

val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val (bir_spinlockfull_progbin_def, bir_spinlockfull_prog_def, bir_is_lifted_prog_spinlockfull) = lift_da_and_store_mc_riscv
          "spinlockfull"
          "spinlockfull.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));


(*****************************************************************************)
(* Helper definitions ********************************************************)
(*****************************************************************************)
(* TODO place these elsewhere *)

Definition core_runs_prog_def:
  core_runs_prog cid s prog =
    ?st. FLOOKUP s cid = SOME $ Core cid prog st
    /\ st = bir_state_init prog
End

(* projection of the state of a core *)

Definition core_def:
  core cid S = THE $ FLOOKUP (FST S) cid
End

Definition core_state_def:
  core_state cid S = get_core_state $ core cid S
End

Definition core_prog_def:
  core_prog cid S = get_core_prog $ core cid S
End

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

Definition core_pc_def:
  core_pc cid S = (core_state cid S).bst_pc
End

(* compare address range *)

Definition addr_val_def:
  addr_val $ BL_Address $ Imm64 v = v
End

Definition core_pc_index_def:
  core_pc_index cid S = SND $ bst_pc_tuple $ core_pc cid S
End

Definition core_pc_lbl_def:
  core_pc_lbl cid S = addr_val $ FST $ bst_pc_tuple $ core_pc cid S
End

Theorem core_zoo =
  LIST_CONJ $
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
  [core_pc_lbl_def,core_pc_def,core_pc_index_def,addr_val_def,bst_pc_tuple_def,core_state_def,get_core_state_def,core_def,core_prog_def]

(* read a variable from a given memory *)

Definition bir_read_mem_var_def:
  bir_read_mem_var mem var env =
    bir_eval_exp
      (BExp_Load (BExp_Den $ BVar mem $ BType_Mem Bit64 Bit8)
        (BExp_Den $ BVar var $ BType_Imm Bit64)
        BEnd_LittleEndian Bit32) env
End

(* read a variable from an environment  *)

Definition bir_read_var_def:
  bir_read_var var env =
    bir_eval_exp (BExp_Den (BVar var (BType_Imm Bit64))) env
End

(* read a variable from a core state *)

Definition bir_read_core_reg_def:
  bir_read_core_reg var cid S =
    bir_read_var var (core_state cid S).bst_environ
End

(* read a zero variable from a core state *)

Definition bir_read_core_reg_zero_def:
  bir_read_core_reg_zero var cid S <=>
    bir_read_core_reg var cid S = SOME $ BVal_Imm $ Imm64 0w
End

(*****************************************************************************)
(* Extracting reachable states of a program **********************************)
(*****************************************************************************)
(* TODO some theorems need further adjustement *)

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Generic =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Generic stm``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Fence =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Fence mo1 mo2``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Branch =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Branch a1 a2 a3``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Expr =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Expr var e``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> CONV_RULE $ ONCE_DEPTH_CONV $ RHS_CONV $ computeLib.EVAL_CONV
  |> GEN_ALL

(*
Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Amo var a_e v_e acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs()]
  |> GEN_ALL
*)

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo:
  !x var a_e v_e acq rel.
  bir_get_stmt bir_spinlockfull_prog x = BirStmt_Amo var a_e v_e acq rel ==> F
Proof
  cheat
QED

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_None =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_None``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [AC CONJ_ASSOC CONJ_COMM]
  |> GEN_ALL

(* TODO calculate is_rel_def,is_amo_def,is_xcl_read_def,is_acq_def *)
Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Read =
  REFL ``bir_get_stmt bir_spinlockfull_prog pc = BirStmt_Read var a_e opt_cast xcl acq rel``
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ REWRITE_CONV [bir_get_stmt_write,bir_get_stmt_read]
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ ONCE_DEPTH_CONV $ REWRITE_CONV [Once bir_spinlockfull_prog_def]
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option"]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss) [bir_program_labelsTheory.BL_Address_HC_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.COND_elim_ss ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss) []
  |> SIMP_RULE (srw_ss()) []
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_read_args_def]

(* TODO calculate is_rel_def,is_amo_def,is_xcl_write_def,is_acq_def *)
Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Write =
  REFL ``bir_get_stmt bir_spinlockfull_prog pc = BirStmt_Write a_e v_e xcl acq rel``
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ REWRITE_CONV [bir_get_stmt_write,bir_get_stmt_read]
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ ONCE_DEPTH_CONV $ REWRITE_CONV [Once bir_spinlockfull_prog_def]
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option"]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss) [bir_program_labelsTheory.BL_Address_HC_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.COND_elim_ss ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss) []
  |> SIMP_RULE (srw_ss()) []
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_fulfil_args_def,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_fulfil_args_def,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_fulfil_args_def,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_fulfil_args_def,get_read_args_def]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss) [EL,get_fulfil_args_def,get_read_args_def]

Theorem bir_get_stmt_bir_spinlockfull_thms =
  LIST_CONJ $
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
    [bir_get_stmt_bir_spinlockfull_prog_BirStmt_Generic,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Fence,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Branch,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Expr,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_None,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Write,
    bir_get_stmt_bir_spinlockfull_prog_BirStmt_Read]

(* pc is reachable for bir_spinlockfull_prog from its first pc *)
(* TODO automate *)

Definition reachable_slf_def:
  reachable_slf pc =
    !bpt. bpt = bst_pc_tuple pc ==>
       bpt = (BL_Address $ Imm64  0w,0n) \/ bpt = (BL_Address $ Imm64  0w,1n)
    \/ bpt = (BL_Address $ Imm64  4w,0n) \/ bpt = (BL_Address $ Imm64  4w,1n)
    \/ bpt = (BL_Address $ Imm64  4w,3n) \/ bpt = (BL_Address $ Imm64  8w,0n)
    \/ bpt = (BL_Address $ Imm64 12w,0n) \/ bpt = (BL_Address $ Imm64 12w,1n)
    \/ bpt = (BL_Address $ Imm64 16w,0n) \/ bpt = (BL_Address $ Imm64 16w,1n)
    \/ bpt = (BL_Address $ Imm64 16w,2n) \/ bpt = (BL_Address $ Imm64 16w,5n)
    \/ bpt = (BL_Address $ Imm64 20w,0n) \/ bpt = (BL_Address $ Imm64 24w,0n)
    \/ bpt = (BL_Address $ Imm64 28w,0n) \/ bpt = (BL_Address $ Imm64 28w,1n)
    \/ bpt = (BL_Address $ Imm64 32w,0n) \/ bpt = (BL_Address $ Imm64 32w,1n)
    \/ bpt = (BL_Address $ Imm64 36w,0n) \/ bpt = (BL_Address $ Imm64 36w,1n)
    \/ bpt = (BL_Address $ Imm64 36w,2n) \/ bpt = (BL_Address $ Imm64 36w,3n)
    \/ bpt = (BL_Address $ Imm64 40w,0n)
End

(* all possible steps of the full spinlock
 * sl_step (block,pc) (block',pc') *)
(* TODO automate *)

Inductive slf_step:
     slf_step (BL_Address $ Imm64  0w,0n) (BL_Address $ Imm64  0w,1n)
  /\ slf_step (BL_Address $ Imm64  0w,1n) (BL_Address $ Imm64  4w,0n)
  /\ slf_step (BL_Address $ Imm64  4w,0n) (BL_Address $ Imm64  4w,1n)
  /\ slf_step (BL_Address $ Imm64  4w,1n) (BL_Address $ Imm64  4w,3n)
  /\ slf_step (BL_Address $ Imm64  4w,3n) (BL_Address $ Imm64  8w,0n)
  /\ slf_step (BL_Address $ Imm64  8w,0n) (BL_Address $ Imm64  4w,0n)
  /\ slf_step (BL_Address $ Imm64  8w,0n) (BL_Address $ Imm64 12w,0n)
  /\ slf_step (BL_Address $ Imm64 12w,0n) (BL_Address $ Imm64 12w,1n)
  /\ slf_step (BL_Address $ Imm64 12w,1n) (BL_Address $ Imm64 16w,0n)
  /\ slf_step (BL_Address $ Imm64 16w,0n) (BL_Address $ Imm64 16w,1n)
  /\ slf_step (BL_Address $ Imm64 16w,1n) (BL_Address $ Imm64 16w,2n)
  /\ slf_step (BL_Address $ Imm64 16w,2n) (BL_Address $ Imm64 16w,5n)
  /\ slf_step (BL_Address $ Imm64 16w,5n) (BL_Address $ Imm64 20w,0n)
  /\ slf_step (BL_Address $ Imm64 20w,0n) (BL_Address $ Imm64  4w,0n)
  /\ slf_step (BL_Address $ Imm64 20w,0n) (BL_Address $ Imm64 24w,0n)
  /\ slf_step (BL_Address $ Imm64 24w,0n) (BL_Address $ Imm64 28w,0n)
  /\ slf_step (BL_Address $ Imm64 28w,0n) (BL_Address $ Imm64 28w,1n)
  /\ slf_step (BL_Address $ Imm64 28w,1n) (BL_Address $ Imm64 32w,0n)
  /\ slf_step (BL_Address $ Imm64 32w,0n) (BL_Address $ Imm64 32w,1n)
  /\ slf_step (BL_Address $ Imm64 32w,1n) (BL_Address $ Imm64 36w,0n)
  /\ slf_step (BL_Address $ Imm64 36w,0n) (BL_Address $ Imm64 36w,1n)
  /\ slf_step (BL_Address $ Imm64 36w,1n) (BL_Address $ Imm64 36w,2n)
  /\ slf_step (BL_Address $ Imm64 36w,2n) (BL_Address $ Imm64 36w,3n)
  /\ slf_step (BL_Address $ Imm64 36w,3n) (BL_Address $ Imm64 40w,0n)
End

(* reachable_slf only transitions from reachable to reachable states *)

Theorem reachable_slf_step_imp:
  !pc pc'. reachable_slf pc
  /\ slf_step (bst_pc_tuple pc) (bst_pc_tuple pc')
  ==> reachable_slf pc'
Proof
  rw[reachable_slf_def]
  >> gvs[slf_step_cases]
QED

(*
Theorem reachable_pc_sim:
  !i tr cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ p = bir_spinlockfull_prog :string bir_program_t
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ bst_pc_tuple st.bst_pc = (BL_Address $ Imm64 36w,3n)
  /\ reachable_slf st.bst_pc
  /\ bst_pc_tuple st.bst_pc <> bst_pc_tuple st'.bst_pc
  ==> XX $ bst_pc_tuple st'.bst_pc
Proof
  rpt gen_tac >> strip_tac
(* the remaining tactic mimick an EVAL for a parstep{_nice,} transition
 * in the context of a concrete program 'bir_spinlock_prog'
 * with the extracted possible pc locations of different instructions
 * encoded in bir_get_stmt_bir_spinlockfull_thms
 *)
  >> fs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE,clstep_cases,bir_programTheory.bir_pc_next_def,bst_pc_tuple_def]
  >> gvs[FLOOKUP_UPDATE,bir_get_stmt_bir_spinlockfull_thms]
  >> gvs[AllCaseEqs(), bir_exec_stmtB_mix_def, bir_exec_stmt_assert_mix_def, bir_exec_stmt_mix_def, bir_expTheory.bir_eval_bin_exp_def, bir_expTheory.bir_eval_bin_pred_def, bir_eval_exp_mix_def, bir_expTheory.bir_eval_exp_def, bir_get_stmt_bir_spinlockfull_thms, bir_programTheory.bir_block_pc_def, bir_programTheory.bir_eval_label_exp_def, bir_programTheory.bir_exec_stmtB_def, bir_programTheory.bir_exec_stmtE_def, bir_programTheory.bir_exec_stmt_assert_def, bir_programTheory.bir_exec_stmt_cjmp_def, bir_programTheory.bir_exec_stmt_def, bir_programTheory.bir_exec_stmt_jmp_def, bir_programTheory.bir_exec_stmt_jmp_to_label_def, bir_programTheory.bir_pc_next_def, bir_programTheory.bir_state_set_typeerror_def, bst_pc_tuple_def, get_fulfil_args_def, get_read_args_def, is_global_def, pairTheory.ELIM_UNCURRY, bir_envTheory.bir_env_read_def]
  >> fs[bir_spinlockfull_prog_is_xcl_read,bir_spinlockfull_prog_is_xcl_write,bir_spinlockfull_prog_not_is_xcl_write]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), bir_exec_stmtB_mix_def, bir_exec_stmt_assert_mix_def, bir_exec_stmt_mix_def, bir_expTheory.bir_eval_bin_exp_def, bir_expTheory.bir_eval_bin_pred_def, bir_eval_exp_mix_def, bir_expTheory.bir_eval_exp_def, bir_get_stmt_bir_spinlockfull_thms, bir_programTheory.bir_block_pc_def, bir_programTheory.bir_eval_label_exp_def, bir_programTheory.bir_exec_stmtB_def, bir_programTheory.bir_exec_stmtE_def, bir_programTheory.bir_exec_stmt_assert_def, bir_programTheory.bir_exec_stmt_cjmp_def, bir_programTheory.bir_exec_stmt_def, bir_programTheory.bir_exec_stmt_jmp_def, bir_programTheory.bir_exec_stmt_jmp_to_label_def, bir_programTheory.bir_pc_next_def, bir_programTheory.bir_state_set_typeerror_def, bst_pc_tuple_def, get_fulfil_args_def, get_read_args_def, is_global_def, pairTheory.ELIM_UNCURRY, bir_envTheory.bir_env_read_def]
QED
*)

Theorem reachable_slf_sim:
  !i tr cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ core_runs_prog cid (FST $ HD tr) bir_spinlockfull_prog
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ reachable_slf st.bst_pc
  ==>
    (bst_pc_tuple st.bst_pc) = (bst_pc_tuple st'.bst_pc)
    \/ slf_step (bst_pc_tuple st.bst_pc) (bst_pc_tuple st'.bst_pc)
Proof
  cheat
QED

(* pc within crit region *)

Definition in_crit_slf_def:
  in_crit_slf pc <=>
    reachable_slf pc
    /\ bst_pc_tuple pc = (BL_Address $ Imm64 32w,0)
End

(* pc within lock region *)

Definition in_lock_slf_def:
  in_lock_slf pc <=>
    reachable_slf pc
    /\ !n x. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
      ==> 0w < x /\ x <= 24w
      \/ (x,n) = (0w,1)
End

(* pc within unlock region *)

Definition in_unlock_slf_def:
  in_unlock_slf pc <=>
    reachable_slf pc
    /\ !x n. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
      ==> 28w < x /\ x < 40w
        \/ x = 28w /\ 0 < n
End

(* pc not in lock or unlock region *)

Definition outside_un_lock_slf_def:
  outside_un_lock_slf pc <=>
    reachable_slf pc
    /\ !x n. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
    ==>  (x,n) = (0w,0)
      \/ 24w < x /\ x < 28w
      \/ (x,n) = (28w,0)
      \/ 40w <= x
End

Theorem reachable_slf_eq:
  !pc. reachable_slf pc
  <=> in_lock_slf pc
    \/ in_unlock_slf pc
    \/ outside_un_lock_slf pc
Proof
  dsimp[in_unlock_slf_def,in_lock_slf_def,outside_un_lock_slf_def,EQ_IMP_THM]
  >> rpt strip_tac
  >> fs[reachable_slf_def,bst_pc_tuple_def]
QED

Theorem reachable_slf_imp:
  (!pc. in_unlock_slf pc ==> ~in_lock_slf pc)
  /\ (!pc. in_lock_slf pc ==> ~outside_un_lock_slf pc)
  /\ (!pc. outside_un_lock_slf pc ==> ~in_unlock_slf pc)
Proof
  rpt gen_tac >> rpt conj_tac >> ntac 2 strip_tac
  >> fs[in_unlock_slf_def,in_lock_slf_def,outside_un_lock_slf_def]
  >> gs[reachable_slf_def,bst_pc_tuple_def]
QED

(* thread  cid  sees a free lock *)

Definition is_free_slf_def:
  is_free_slf cid S <=>
    bir_read_mem_var "MEM8" "x7" ((core_state cid S).bst_environ)
    = SOME $ BVal_Imm $ Imm64 0w
End

val _ = export_theory();
