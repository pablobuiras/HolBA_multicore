
open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "spinlock2";

val (bir_spinlock_progbin_def, bir_spinlock_prog_def, bir_is_lifted_prog_spinlock) = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory tracesTheory;
open finite_mapTheory;
open spinlockTheory;

(* simplifying terms through rewrites *)

Triviality CONJ_EQ_NEQ_ELIM:
  (!x v' v. x = v /\ x <> v' <=> x = v /\ v <> v')
  /\ (!x v' v. x <> v' /\ x = v  <=> x = v /\ v <> v')
  /\ (!x v' v A. x = v /\ x <> v' /\ A <=> x = v /\ v <> v' /\ A)
  /\ (!x v' v A. x <> v' /\ x = v /\ A <=> v <> v' /\ x = v /\ A)
  /\ (!x v' v B. B /\ x = v /\ x <> v' <=> B /\ x = v /\ v <> v')
  /\ (!x v' v B. B /\ x <> v' /\ x = v <=> B /\ v <> v' /\ x = v )
  /\ (!x v' v B. x = v /\ B /\ x <> v' <=> x = v /\ B /\ v <> v')
  /\ (!x v' v B. x <> v' /\ B /\ x = v <=> v <> v' /\ B /\ x = v)
  /\ (!x v' v A B. x = v /\ B /\ x <> v' /\ A <=> x = v /\ B /\ v <> v' /\ A)
  /\ (!x v' v A B. x <> v' /\ B /\ x = v /\ A <=> v <> v' /\ B /\ x = v /\ A)
  /\ (!x v' v A B. B /\ x = v /\ x <> v' /\ A <=> B /\ x = v /\ v <> v' /\ A)
  /\ (!x v' v A B. B /\ x <> v' /\ x = v /\ A <=> B /\ v <> v' /\ x = v /\ A)
Proof
  fs[EQ_IMP_THM]
QED

Theorem ELIM_thms:
  !P.
  (!x v. x = v /\ P x <=> P v /\ x = v)
  /\ (!x v. P x /\ x = v  <=> P v /\ x = v)

  /\ (!x v A. x = v /\ A /\ P x <=> P v /\ x = v /\ A)
  /\ (!x v A. x = v /\ P x /\ A <=> P v /\ x = v /\ A)
  /\ (!x v A. P x /\ x = v /\ A <=> P v /\ x = v /\ A)
  /\ (!x v A. P x /\ A /\ x = v <=> P v /\ x = v /\ A)

  /\ (!x v A B. B /\ x = v /\ A /\ P x <=> P v /\ x = v /\ B /\ A)
  /\ (!x v A B. B /\ x = v /\ P x /\ A <=> P v /\ x = v /\ B /\ A)
  /\ (!x v A B. B /\ P x /\ x = v /\ A <=> P v /\ x = v /\ B /\ A)
  /\ (!x v A B. B /\ P x /\ A /\ x = v <=> P v /\ x = v /\ B /\ A)

  /\ (!x v A B C. B /\ x = v /\ C /\ P x /\ A <=> P v /\ x = v /\ B /\ C /\ A)
Proof
  fs[EQ_IMP_THM]
QED

(* generates various conjunction theorems with given term *)
(*
 val term = ``λx. v = x``
 val term = ``λx. get_read_args v = x``
  fun_eq_conjs term
 *)
fun fun_eq_conjs term =
  let
    val ty = type_of term
    val thm = 
      ISPEC term ELIM_thms 
      (* int_arithTheory.CONJ_EQ_ELIM *)
      |> SIMP_RULE (std_ss) []
  in
    map GEN_ALL $ CONJUNCTS thm
  end

(* conversion to removing evident inequalities, like  a <> 2
 * in  |- P a <=> a = 1 /\ a <> 2  *)
val CONJ_EQ_NEQ_conv = REPEATC $
  ONCE_DEPTH_CONV (REWRITE_CONV $ CONJUNCTS CONJ_EQ_NEQ_ELIM)
  THENC (SIMP_CONV (srw_ss()) [])
  THENC
  ONCE_DEPTH_CONV (REWRITE_CONV $ fun_eq_conjs ``λx. x:num <> v'``)
  THENC (SIMP_CONV (srw_ss()) [])
  THENC ONCE_DEPTH_CONV (REWRITE_CONV $ fun_eq_conjs ``λx. x:bir_label_t <> v'``)
  THENC (SIMP_CONV (srw_ss()) [])
  THENC ONCE_DEPTH_CONV (REWRITE_CONV $ fun_eq_conjs ``λi. EL i ls = x``)
  THENC (SIMP_CONV (srw_ss()) [])
  THENC ONCE_DEPTH_CONV (REWRITE_CONV $ fun_eq_conjs ``λe. get_fulfil_args e = x``)
  THENC (SIMP_CONV (srw_ss()) [])
  THENC ONCE_DEPTH_CONV (REWRITE_CONV $ fun_eq_conjs ``λe. get_read_args e = x``)
  THENC (SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [AC CONJ_ASSOC CONJ_COMM]) ;

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Generic =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_Generic stm``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Fence =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_Fence mo1 mo2``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Branch =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_Branch a1 a2 a3``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Expr =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_Expr var e``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_None =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_None``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Definition init_def:
  init cores =
    !cid p st. FLOOKUP cores cid = SOME $ Core cid p st
      ==> st.bst_pc = <| bpc_index := 0; bpc_label := BL_Address $ Imm64 0w |>
End

Theorem reachable_pc:
  !i tr cid p st. wf_trace tr
  /\ i < LENGTH tr
  /\ init (FST $ HD tr)
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> st.bst_pc IN {
    <|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 0w); bpc_index := 1|>;
    <|bpc_label := BL_Address (Imm64 4w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 4w); bpc_index := 1|>;
    <|bpc_label := BL_Address (Imm64 8w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 8w); bpc_index := 1|>;
    <|bpc_label := BL_Address (Imm64 12w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 12w); bpc_index := 1|>;
    <|bpc_label := BL_Address (Imm64 12w); bpc_index := 3|>;
    <|bpc_label := BL_Address (Imm64 16w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 20w); bpc_index := 0|>;
    <|bpc_label := BL_Address (Imm64 20w); bpc_index := 1|>;
    <|bpc_label := BL_Address (Imm64 20w); bpc_index := 2|>;
    <|bpc_label := BL_Address (Imm64 20w); bpc_index := 5|>;
    <|bpc_label := BL_Address (Imm64 24w); bpc_index := 0|>
  }
Proof
  Induct
  >- (rw[init_def] >> res_tac >> fs[])
  >> rw[]
  >> drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> first_x_assum $ drule_then $ drule_at_then Any assume_tac
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> reverse $ Cases_on `parstep_nice cid (EL i tr) (EL (SUC i) tr)`
  >- (
    drule_all_then assume_tac wf_trace_NOT_parstep_nice_state_EQ'
    >> gs[]
  )
  >>  gvs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE,clstep_cases,bir_get_stmt_bir_spinlock_prog_BirStmt_Fence]
  >> map_every (imp_res_tac o (
      CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV $ SYM_CONV)
    ) o iffLR)
    [bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Expr]
  >> asm_rewrite_tac[]
  >> simp[bir_programTheory.bir_pc_next_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> imp_res_tac bir_get_stmt_bir_spinlock_prog
  >> gns[]
  >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_programcounter_t_component_equality,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_bir_spinlock_prog,bir_programTheory.bir_block_pc_def,get_fulfil_args_def,get_read_args_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_state_is_terminated_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_programTheory.bir_pc_next_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_programcounter_t_component_equality,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_bir_spinlock_prog,bir_programTheory.bir_block_pc_def,get_fulfil_args_def,get_read_args_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_state_is_terminated_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_programTheory.bir_pc_next_def]
QED

val _ = export_theory();
