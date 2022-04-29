
open HolKernel Parse boolLib bossLib;

open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib bir_promisingTheory ;
open tracesTheory tracestepTheory spinlockTheory;

(*
 * spinlock correctness proof
 *)

val _ = new_theory "spinlock2";

(*
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val (bir_spinlockfull_progbin_def, bir_spinlockfull_prog_def, bir_is_lifted_prog_spinlockfull) = lift_da_and_store_mc_riscv
          "spinlockfull"
          "spinlockfull.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
*)

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

(*
bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ
bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ
*)

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Amo =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_Amo var a_e v_e acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs()]

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_None =
  EVAL ``bir_get_stmt bir_spinlock_prog x = BirStmt_None``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> CONV_RULE CONJ_EQ_NEQ_conv
  |> GEN_ALL

Theorem bir_get_spinlock_stmts =
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
      [bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Fence,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,
      bir_get_stmt_bir_spinlock_prog_BirStmt_None,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Amo,
      bir_get_stmt_bir_spinlock_prog_BirStmt_Expr]
  |> LIST_CONJ

Definition init1_def:
  init1 st <=>
    st.bst_pc = <| bpc_index := 0; bpc_label := BL_Address $ Imm64 0w |>
End

Definition init_def:
  init cores =
    !cid p st. FLOOKUP cores cid = SOME $ Core cid p st ==> init1 st
End

Theorem core_runs_spinlock_init1:
  !cid cores. core_runs_spinlock cid cores
  ==> ?st. FLOOKUP cores cid = SOME $ Core cid bir_spinlock_prog st /\ init1 st
Proof
  rw[init1_def,core_runs_spinlock_def,core_runs_prog_def]
  >> fs[bir_programTheory.bir_state_init_def,bir_programTheory.bir_pc_first_def,bir_spinlock_prog_def,bir_programTheory.bir_block_pc_def,bir_program_labelsTheory.BL_Address_HC_def]
QED

Theorem cores_run_spinlock_init:
  !tr. cores_run_spinlock $ FST $ HD tr ==> init $ FST $ HD tr
Proof
  rw[cores_run_spinlock_def,init_def]
  >> res_tac
  >> imp_res_tac core_runs_spinlock_init1
  >> gs[]
QED

(*
  all possible steps with the spinlock
  sl_step (blck,pc) (blck',pc')
*)
Inductive sl_step:
  sl_step (BL_Address $ Imm64 x,y) (BL_Address $ Imm64 x,y)
  /\ sl_step (BL_Address $ Imm64 0w,0n) (BL_Address $ Imm64 0w,1)
  /\ sl_step (BL_Address $ Imm64 0w,1)  (BL_Address $ Imm64 4w,0)
  /\ sl_step (BL_Address $ Imm64 4w,0)  (BL_Address $ Imm64 4w,1)
  /\ sl_step (BL_Address $ Imm64 4w,1)  (BL_Address $ Imm64 8w,0)
  /\ sl_step (BL_Address $ Imm64 8w,0)  (BL_Address $ Imm64 8w,1)
  /\ sl_step (BL_Address $ Imm64 8w,1)  (BL_Address $ Imm64 12w,0)
  /\ sl_step (BL_Address $ Imm64 12w,0) (BL_Address $ Imm64 12w,1)
  /\ sl_step (BL_Address $ Imm64 12w,1) (BL_Address $ Imm64 12w,3)
  /\ sl_step (BL_Address $ Imm64 12w,3) (BL_Address $ Imm64 16w,0)
  /\ sl_step (BL_Address $ Imm64 16w,0) (BL_Address $ Imm64 12w,0)
  /\ sl_step (BL_Address $ Imm64 16w,0) (BL_Address $ Imm64 20w,0)
  /\ sl_step (BL_Address $ Imm64 20w,0) (BL_Address $ Imm64 20w,1)
  /\ sl_step (BL_Address $ Imm64 20w,1) (BL_Address $ Imm64 20w,2)
  /\ sl_step (BL_Address $ Imm64 20w,2) (BL_Address $ Imm64 20w,5)
  /\ sl_step (BL_Address $ Imm64 20w,5) (BL_Address $ Imm64 24w,0)
  /\ sl_step (BL_Address $ Imm64 24w,0) (BL_Address $ Imm64 12w,0)
  /\ sl_step (BL_Address $ Imm64 24w,0) (BL_Address $ Imm64 28w,0)
End

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

(*
(*
  TODO make this a function taking a term:
  val term = ``sl_step``
 *)
val fun_snd_imp =
  let
    val values =
      map (rand o concl o SPEC_ALL) $ CONJUNCTS sl_step_rules
    val term' =
      mk_imp (``sl_step å1 å2``,
        map (fn value => mk_eq (``å2:bir_label_t # num``, value)) values
        |> list_mk_disj)
  in
   prove(term', dsimp[sl_step_cases])
  end
*)

Definition reachable_pc_def:
  reachable_pc pc <=>
    !bpt. bpt = bst_pc_tuple pc ==>
    bpt = (BL_Address $ Imm64 0w,1) \/ bpt = (BL_Address $ Imm64 4w,0) \/
    bpt = (BL_Address $ Imm64 4w,1) \/ bpt = (BL_Address $ Imm64 8w,0) \/
    bpt = (BL_Address $ Imm64 8w,1) \/ bpt = (BL_Address $ Imm64 12w,0) \/
    bpt = (BL_Address $ Imm64 12w,1) \/ bpt = (BL_Address $ Imm64 12w,3) \/
    bpt = (BL_Address $ Imm64 16w,0) \/ bpt = (BL_Address $ Imm64 20w,0) \/
    bpt = (BL_Address $ Imm64 20w,1) \/ bpt = (BL_Address $ Imm64 20w,2) \/
    bpt = (BL_Address $ Imm64 20w,5) \/ bpt = (BL_Address $ Imm64 24w,0) \/
    bpt = (BL_Address $ Imm64 28w,0) \/ bpt = (BL_Address $ Imm64 0w,0)
End

Theorem reachable_pc_sl_step_imp:
  !pc pc'. reachable_pc pc
  /\ sl_step (bst_pc_tuple pc) (bst_pc_tuple pc')
  ==> reachable_pc pc'
Proof
  rw[reachable_pc_def]
  >> gvs[sl_step_cases]
QED

Theorem reachable_pc_sim:
  !i tr cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ reachable_pc st.bst_pc
  ==> sl_step (bst_pc_tuple st.bst_pc) (bst_pc_tuple st'.bst_pc)
Proof
  rpt gen_tac >> strip_tac
  >> reverse $ Cases_on `parstep_nice cid (EL i tr) (EL (SUC i) tr)`
  >- (
    drule_all_then assume_tac wf_trace_NOT_parstep_nice_state_EQ'
    >> fs[]
    >> gvs[sl_step_rules,reachable_pc_def]
  )
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
(* the remaining tactic mimick an EVAL for a parstep{_nice,} transition
 * in the context of a concrete program 'bir_spinlock_prog'
 * with the extracted possible pc locations of different instructions
 * encoded in bir_get_stmt_bir_spinlock_prog_BirStmt_*
 *)
  >> fs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE,clstep_cases,bir_programTheory.bir_pc_next_def,bst_pc_tuple_def,sl_step_cases]
  >> gvs[FLOOKUP_UPDATE,bir_get_spinlock_stmts]
  >> gvs[bir_programTheory.bir_pc_next_def,AllCaseEqs(),bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_None,bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,bir_programTheory.bir_exec_stmt_cjmp_def,bst_pc_tuple_def,reachable_pc_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_programTheory.bir_pc_next_def,AllCaseEqs(),bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_None,bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,get_fulfil_args_def,get_read_args_def]
QED

Theorem wf_trace_reachable_pc:
  !i tr cid p st st'. wf_trace tr
  /\ i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> reachable_pc st.bst_pc
Proof
  Induct >> rpt strip_tac
  >- (
    imp_res_tac core_runs_spinlock_init1
    >> gs[bst_pc_tuple_def,reachable_pc_def,init1_def]
  )
  >> rev_drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> first_x_assum $ drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> gs[]
  >> drule_all_then assume_tac reachable_pc_sim
  >> dxrule_all reachable_pc_sl_step_imp
  >> fs[]
QED

Theorem reachable_pc_sl_step:
  !i tr cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> reachable_pc st.bst_pc
    /\ reachable_pc st'.bst_pc
    /\ sl_step (bst_pc_tuple st.bst_pc) (bst_pc_tuple st'.bst_pc)
Proof
  rpt gen_tac >> strip_tac
  >> rev_drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac wf_trace_reachable_pc
  >> drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac wf_trace_reachable_pc
  >> gs[]
  >> rev_drule_all_then irule reachable_pc_sim
QED

Theorem bir_env_def_spinlock =
  EVAL ``bir_env_default $ bir_envty_of_vs $ bir_varset_of_program bir_spinlock_prog``
  |> SIMP_RULE (srw_ss()) [PULL_FORALL,bir_valuesTheory.bir_default_value_of_type_def,combinTheory.o_DEF,pred_setTheory.DIFF_DEF,bir_envTheory.bir_var_type_def,COND_RAND]

(* unique properties *)

Definition unique_def:
  unique fmap P =
    !id id' x x'. FLOOKUP fmap id = SOME x /\ P x
      /\ FLOOKUP fmap id' = SOME x' /\ P x'
      ==> id = id'
End

Theorem FLOOKUP_NOT_unique_eq:
  !P cores cid st st'. FLOOKUP cores cid = SOME st
  /\ ~(P st) /\ ~(P st')
  ==> unique (FUPDATE cores (cid,st')) P = unique cores P
Proof
  rw[unique_def,EQ_IMP_THM]
  >- (
    first_x_assum irule
    >> dsimp[FLOOKUP_UPDATE,AllCaseEqs()]
    >> conj_tac >> spose_not_then assume_tac >> gvs[]
  )
  >> gs[FLOOKUP_UPDATE,AllCaseEqs()]
QED

Theorem FLOOKUP_unique_eq:
  FLOOKUP cores cid = SOME st
  /\ P st /\ P st'
  ==> unique (FUPDATE cores (cid,st')) P = unique cores P
Proof
  rw[unique_def,EQ_IMP_THM]
  >- (
    first_x_assum irule
    >> dsimp[FLOOKUP_UPDATE,AllCaseEqs(),LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR]
    >> metis_tac[]
  )
  >> gs[FLOOKUP_UPDATE,AllCaseEqs()]
QED

(* invariant *)

Definition in_crit_def:
  in_crit (Core id p st) <=>
    st.bst_pc = <|bpc_label := BL_Address (Imm64 28w); bpc_index := 0|>
End

Theorem in_crit_sl_step:
  !cid p st st'.
  sl_step (bst_pc_tuple st.bst_pc) (bst_pc_tuple st'.bst_pc)
  /\ st.bst_pc <> st'.bst_pc
  /\ ~(in_crit $ Core cid p st')
  ==> ~(in_crit $ Core cid p st)
Proof
  rw[sl_step_cases,in_crit_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> gvs[]
QED

Theorem in_crit_reachable_pc:
  in_crit $ Core cid p st
  ==> reachable_pc st.bst_pc
Proof
  fs[in_crit_def,reachable_pc_def,bst_pc_tuple_def]
QED

Definition invariant_def:
  invariant cores = unique cores in_crit
End

Theorem init_unique_in_crit_imp:
  !i tr. wf_trace tr /\ wf_trace1 tr
  /\ init (FST $ HD tr)
  ==> invariant (FST $ HD tr)
Proof
  rw[init1_def,init_def,invariant_def,unique_def,Excl"EL",GSYM EL,Excl"EL_restricted"]
  >> drule_then drule wf_trace1_FLOOKUP
  >> drule_then rev_drule wf_trace1_FLOOKUP
  >> rw[wf_trace_NOT_NULL,LENGTH_NOT_NULL]
  >> fs[in_crit_def]
  >> qpat_x_assum `!cid p st. FLOOKUP _ _ = _ ==> _` imp_res_tac
  >> gs[]
QED

(* no loops in the spinlock program *)

val pc_inc_tac =
  spose_not_then kall_tac
  >> fs[bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality]
  >> rpt $ qpat_x_assum `_.bst_pc.bpc_label = _` mp_tac
  >> rpt $ qpat_x_assum `_.bst_pc.bpc_index = _` mp_tac
  >> rpt $ first_x_assum kall_tac
  >> rpt strip_tac
  >> BasicProvers.every_case_tac
  >> fs[bir_programTheory.bir_pc_next_def] ;

Theorem parstep_sl_step_progress:
  !tr i cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME (Core cid p st)
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME (Core cid p st')
  /\ sl_step (bst_pc_tuple st.bst_pc) (bst_pc_tuple st'.bst_pc)
  /\ ~is_promise cid (LENGTH (SND (EL i tr)) + 1) (EL i tr) (EL (SUC i) tr)
  ==> st.bst_pc <> st'.bst_pc
Proof
  rpt gen_tac >> strip_tac
  >> fs[progressing_trace_def,progressing_def]
  >> first_x_assum $ drule_then drule
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> reverse $ gvs[parstep_nice_def,parstep_cases,cstep_cases,FLOOKUP_UPDATE]
  >- gs[is_promise_def,FLOOKUP_UPDATE,bir_promisingTheory.mem_msg_t_component_equality]
  >> PRED_ASSUM is_neg kall_tac
  >> fs[Once MONO_NOT_EQ] >> strip_tac
  >> drule wf_trace_reachable_pc
  >> rpt $ disch_then drule
  >> disch_then assume_tac
  >> fs[clstep_cases]
  >- pc_inc_tac
  >- pc_inc_tac
  >- pc_inc_tac
  >- pc_inc_tac
  >- pc_inc_tac
  >- (
    (* branch *)
    gvs[bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,FLOOKUP_UPDATE]
    >> cheat
  )
  >- pc_inc_tac
  >- (
    gvs[FLOOKUP_UPDATE]
    >> spose_not_then kall_tac
    >> gvs[bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,FLOOKUP_UPDATE,bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality]
    >> cheat (* evaluate statements that change the pc *)
  )
QED

(* no promises possible after a certain program counter *)
(* TODO *)

Theorem core_runs_spinlock_fulfils:
  !tr i cid p st st' t. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==>
      (bst_pc_tuple st.bst_pc = (BL_Address (Imm64 12w),2)
      /\ bst_pc_tuple st'.bst_pc = (BL_Address (Imm64 12w),3))
      (* ~rel ~acq ~xcl, loc = ...*)
    \/ (
     bst_pc_tuple st.bst_pc = (BL_Address (Imm64 20w),2)
     /\ bst_pc_tuple st'.bst_pc = (BL_Address (Imm64 20w),5)
      (* ~rel ~acq xcl, loc = ...*)
      (* bir_eval_exp_view (BExp_Den spinlock_var) s.bst_environ s.bst_viewenv *)
    )
Proof
  rpt strip_tac
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> drule_all_then strip_assume_tac is_fulfil_parstep_nice_eq
  >> gvs[FLOOKUP_UPDATE,bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bst_pc_tuple_def,bir_programTheory.bir_pc_next_def]
QED

(* a core with a non-initial pc has progressed *)

Theorem core_runs_spinlock_NOT_init_pc:
  !tr i cid p st. wf_trace tr
  /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ ~init1 st
  ==> ~same_state_prop_range cid tr 0 i I
Proof
  rpt strip_tac
  >> drule_all_then assume_tac same_state_prop_indexes
  >> drule_all_then assume_tac core_runs_spinlock_init1
  >> gs[same_state_prop_def]
QED

Theorem xclfail_update_envs:
  !new_viewenv new_env st.
  bst_pc_tuple st.bst_pc = (BL_Address (Imm64 20w),2)
  /\ SOME new_viewenv = xclfail_update_viewenv bir_spinlock_prog st
  /\ SOME new_env = xclfail_update_env bir_spinlock_prog st
  ==> new_viewenv = st.bst_viewenv |+ (BVar "x6" (BType_Imm Bit64),0) /\
    SOME new_env = bir_env_update (bir_var_name (BVar "x6" (BType_Imm Bit64)))
      (BVal_Imm (Imm64 1w)) (bir_var_type (BVar "x6" (BType_Imm Bit64)))
      st.bst_environ
Proof
  rpt gen_tac
  >> fs[GSYM AND_IMP_INTRO]
  >> strip_tac
  >> EVAL_TAC
  >> fs[bst_pc_tuple_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def]
QED

Theorem in_crit_before3:
  !tr i cid p st x.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p st)
  /\  bst_pc_tuple st.bst_pc = (BL_Address (Imm64 20w),5)
  /\ bir_eval_unary_exp BIExp_Not
    (bir_eval_bin_pred BIExp_Equal
      (bir_env_read (BVar "x6" (BType_Imm Bit64)) st.bst_environ)
      (SOME (BVal_Imm (Imm64 0w)))) = SOME x
  /\ bir_dest_bool_val x = SOME F
  ==> ?j st' t. j < i
     /\ parstep_nice cid (EL j tr) (EL (SUC j) tr)
     /\ same_state_prop_range cid tr (SUC j) i I
     /\ ~is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)
     /\ FLOOKUP (FST (EL j tr)) cid = SOME (Core cid p st')
     /\ FLOOKUP (FST (EL (SUC j) tr)) cid = SOME (Core cid p st)
     /\ bst_pc_tuple st'.bst_pc = (BL_Address (Imm64 20w),2)
     /\ bir_get_stmt (bir_spinlock_prog :string bir_program_t) st'.bst_pc =
        BirStmt_Write (BExp_Den (BVar "x7" (BType_Imm Bit64)))
          (BExp_Cast BIExp_LowCast (BExp_Const (Imm64 0w)) Bit32) T F F
     /\ is_fulfil_xcl cid t (EL j tr) (FST $ EL (SUC j) tr)
     /\ t < LENGTH (SND $ EL j tr) + 1
     /\ (EL (PRE t) (SND $ EL j tr)).cid = cid
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac previous_state_change
  >- (
    drule core_runs_spinlock_NOT_init_pc
    >> rpt $ disch_then $ drule_at Any
    >> fs[init1_def,bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality,bst_pc_tuple_def]
  )
  >> Cases_on `i` >> fs[]
  >> Cases_on `is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)`
  >- (
    cheat (* any such new promise cannot be fulfiled *)
  )
  >> drule_all_then assume_tac same_state_prop_indexes
  >> drule_at (Pat `FLOOKUP _ _ = _`)  wf_trace_cid_backward
  >> disch_then (fn thm =>
    qspec_then `j` assume_tac thm
    >> qspec_then `SUC j` assume_tac thm)
  >> gvs[same_state_prop_def]
  >> qhdtm_assum `parstep_nice` $ irule_at Any
  >> fs[]
  >> drule_at_then (Pat `parstep_nice _ _ _`) assume_tac parstep_sl_step_progress
  >> drule_at_then (Pat `FLOOKUP (FST $ EL (SUC _) _) _ = _`) assume_tac reachable_pc_sl_step
  >> gs[GSYM PULL_EXISTS]
  >> qpat_x_assum `reachable_pc st.bst_pc` kall_tac
  >> conj_asm1_tac
  >- gs[sl_step_cases,in_crit_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> conj_asm1_tac
  >- (
    fs[bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality,spinlock_var_def,bir_promisingTheory.is_amo_def,bir_get_program_block_info_by_label']
(*
   alternatively:
   EVAL_TAC >> fs[bst_pc_tuple_def,get_read_args_def,get_fulfil_args_def]
*)
  )
  >> qhdtm_x_assum `sl_step` kall_tac
  >> qhdtm_x_assum `reachable_pc` kall_tac
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> gvs[is_fulfil_xcl_def,parstep_nice_def,parstep_cases,FLOOKUP_UPDATE,cstep_cases,clstep_cases]
  >- (
    (* the exclusive write is successful *)
    drule_all_then assume_tac xclfail_update_envs
    >> Cases_on `st''.bst_environ`
    >> gvs[bir_programTheory.bir_pc_next_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality,bir_envTheory.bir_env_update_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def]
    >> qpat_x_assum `bir_eval_unary_exp _ _ = _` mp_tac
    >> EVAL_TAC >> strip_tac
    >> fs[bir_valuesTheory.bir_dest_bool_val_def]
  )
  >> qpat_assum `MEM _ _` $ irule_at Any
  >> fs[PRE_SUB1]
  >> spose_not_then assume_tac
  >> fs[bir_get_stmt_write,fulfil_atomic_ok_def]
QED

Theorem in_crit_before2:
  !tr i cid p st x.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p st)
  /\ bst_pc_tuple st.bst_pc = (BL_Address (Imm64 24w),0)
  /\ bir_eval_unary_exp BIExp_Not
    (bir_eval_bin_pred BIExp_Equal
      (bir_env_read (BVar "x6" (BType_Imm Bit64)) st.bst_environ)
      (SOME (BVal_Imm (Imm64 0w)))) = SOME x
  /\ bir_dest_bool_val x = SOME F
  ==> ?j st'. j < i
    /\ parstep_nice cid (EL j tr) (EL (SUC j) tr)
    /\ same_state_prop_range cid tr (SUC j) i I
    /\ ~is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)
    /\ FLOOKUP (FST (EL j tr)) cid = SOME (Core cid p st')
    /\ FLOOKUP (FST (EL (SUC j) tr)) cid = SOME (Core cid p st)
    /\ bst_pc_tuple st'.bst_pc = (BL_Address (Imm64 20w),5)
    /\ st.bst_environ = st'.bst_environ
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac previous_state_change
  >- (
    drule core_runs_spinlock_NOT_init_pc
    >> rpt $ disch_then $ drule_at Any
    >> fs[init1_def,bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality,bst_pc_tuple_def]
  )
  >> Cases_on `i` >> fs[]
  >> Cases_on `is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)`
  >- (
    cheat (* any such new promise cannot be fulfiled *)
  )
  >> drule_all_then assume_tac same_state_prop_indexes
  >> drule_at (Pat `FLOOKUP _ _ = _`)  wf_trace_cid_backward
  >> disch_then (fn thm =>
    qspec_then `j` assume_tac thm
    >> qspec_then `SUC j` assume_tac thm)
  >> gvs[same_state_prop_def]
  >> qhdtm_assum `parstep_nice` $ irule_at Any
  >> fs[]
  >> drule_at_then (Pat `parstep_nice _ _ _`) assume_tac parstep_sl_step_progress
  >> drule_at_then (Pat `FLOOKUP (FST $ EL (SUC _) _) _ = _`) assume_tac reachable_pc_sl_step
  >> gs[]
  >> qpat_x_assum `reachable_pc st.bst_pc` kall_tac
  >> conj_asm1_tac
  >- gs[sl_step_cases,in_crit_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> `bir_get_stmt (bir_spinlock_prog :string bir_program_t) st''.bst_pc =
        BirStmt_Generic
          (BStmtE (BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))))`
    by fs[bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,bst_pc_tuple_def]
  >> qhdtm_x_assum `sl_step` kall_tac
  >> qhdtm_x_assum `reachable_pc` kall_tac
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> gvs[parstep_nice_def,parstep_cases,cstep_cases,clstep_cases,FLOOKUP_UPDATE]
  >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,bir_programTheory.bir_exec_stmt_cjmp_def,bst_pc_tuple_def]
  >> BasicProvers.every_case_tac
  >> gs[bir_programTheory.bir_programcounter_t_component_equality,CaseEq"option"]
QED

(* properties about the step before entering in_crit *)

Theorem in_crit_before1:
  !tr i cid p st.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p st)
  /\ in_crit (Core cid p st)
  ==> ?j st' x. j < i
    /\ parstep_nice cid (EL j tr) (EL (SUC j) tr)
    /\ same_state_prop_range cid tr (SUC j) i I
    /\ ~is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)
    /\ FLOOKUP (FST (EL j tr)) cid = SOME (Core cid p st')
    /\ FLOOKUP (FST (EL (SUC j) tr)) cid = SOME (Core cid p st)
    /\ bst_pc_tuple st'.bst_pc = (BL_Address (Imm64 24w),0)
    /\ bir_eval_unary_exp BIExp_Not
      (bir_eval_bin_pred BIExp_Equal
        (bir_env_read (BVar "x6" (BType_Imm Bit64)) st'.bst_environ)
        (SOME (BVal_Imm (Imm64 0w)))) = SOME x
    /\ bir_dest_bool_val x = SOME F
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac previous_state_change
  >- (
    drule core_runs_spinlock_NOT_init_pc
    >> rpt $ disch_then $ drule_at Any
    >> fs[init1_def,bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality,bst_pc_tuple_def,in_crit_def]
  )
  >> Cases_on `i` >> fs[]
  >> Cases_on `is_promise cid (LENGTH (SND (EL j tr)) + 1) (EL j tr) (EL (SUC j) tr)`
  >- (
    cheat (* any such new promise cannot be fulfiled *)
  )
  >> drule_all_then assume_tac same_state_prop_indexes
  >> drule_at (Pat `FLOOKUP _ _ = _`)  wf_trace_cid_backward
  >> disch_then (fn thm =>
    qspec_then `j` assume_tac thm
    >> qspec_then `SUC j` assume_tac thm)
  >> gvs[same_state_prop_def]
  >> qhdtm_assum `parstep_nice` $ irule_at Any
  >> fs[]
  >> drule_at_then (Pat `parstep_nice _ _ _`) assume_tac parstep_sl_step_progress
  >> drule_at_then (Pat `FLOOKUP (FST $ EL (SUC _) _) _ = _`) assume_tac reachable_pc_sl_step
  >> gs[GSYM PULL_EXISTS]
  >> qpat_x_assum `reachable_pc st.bst_pc` kall_tac
  >> conj_asm1_tac
  >- gs[sl_step_cases,in_crit_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> `bir_get_stmt (bir_spinlock_prog :string bir_program_t) st''.bst_pc = BirStmt_Branch
    (BExp_UnaryExp BIExp_Not
      (BExp_BinPred BIExp_Equal
          (BExp_Den $ BVar "x6" $ BType_Imm Bit64)
          $ BExp_Const $ Imm64 0w))
    (BLE_Label $ BL_Address $ Imm64 12w)
    $ BLE_Label $ BL_Address $ Imm64 28w`
    by fs[bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,bst_pc_tuple_def]
  >> qhdtm_x_assum `sl_step` kall_tac
  >> qhdtm_x_assum `reachable_pc` kall_tac
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP
  >> gvs[parstep_nice_def,parstep_cases,cstep_cases,clstep_cases,FLOOKUP_UPDATE]
  >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,bir_programTheory.bir_exec_stmt_cjmp_def,bst_pc_tuple_def,in_crit_def]
  >> BasicProvers.every_case_tac
  >> gs[bir_programTheory.bir_programcounter_t_component_equality,CaseEq"option"]
QED

(* a core in the critical section has executed a successful exclusive fulfil *)

Theorem in_crit_is_fulfil_xcl:
  !tr i cid p st.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p st)
  /\ in_crit (Core cid p st)
  ==> ?j t. j < i
    /\ is_fulfil_xcl cid t (EL j tr) (FST $ EL (SUC j) tr)
     /\ t < LENGTH (SND $ EL j tr) + 1
     /\ cid = (EL (PRE t) (SND $ EL j tr)).cid
(*     /\ loc = (EL (PRE t) (SND $ EL j tr)).loc *)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac in_crit_before1
  >> drule_at (Pat `bst_pc_tuple _ = _`) in_crit_before2
  >> disch_then $ drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> gs[]
  >> drule_at (Pat `bst_pc_tuple _ = _`) in_crit_before3
  >> disch_then $ drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> gs[]
  >> goal_assum $ drule_at $ Pat `is_fulfil_xcl _ _ _ _`
  >> fs[]
QED

Theorem is_fulfil_xcl_bst_xclb_less_timestamp:
  !tr i cid p st t. wf_trace tr /\ SUC i < LENGTH tr
  /\ progressing_trace tr
  /\ is_fulfil_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> IS_SOME st.bst_xclb /\ (THE st.bst_xclb).xclb_view < t
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then strip_assume_tac is_fulfil_xcl_is_fulfil
  >> dxrule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_parstep_nice_eq
  >> gvs[FLOOKUP_UPDATE,is_fulfil_xcl_def,get_xclb_view_def,optionTheory.IS_SOME_EXISTS]
QED

Theorem mem_read_EL_SND_loc:
  !t M l. 0 < t /\ IS_SOME $ mem_read M l t
  /\ PRE t < LENGTH M
  ==> l = (EL (PRE t) M).loc
Proof
  Cases >> fs[mem_read_def,oEL_THM] >> Induct
  >> rw[oEL_def,optionTheory.IS_SOME_EXISTS,mem_read_aux_def]
QED

Theorem bst_fwdb_init:
  !l cores cid p st.
  FLOOKUP cores cid = SOME $ Core cid p st
  /\ core_runs_spinlock cid cores
  ==> st.bst_fwdb l = <|fwdb_time := 0; fwdb_view := 0; fwdb_xcl := F|>
Proof
  EVAL_TAC >> rpt strip_tac
  >> gvs[]
QED

Theorem parstep_nice_NOT_is_fulfil_bst_fwdb_eq:
  !tr i cid p st st' t.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ progressing_trace tr
  /\ parstep_nice cid (EL i tr) (EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  /\ (!t. ~is_fulfil cid t (EL i tr) (FST $ EL (SUC i) tr))
  /\ (!t. ~is_amo cid t (EL i tr) (FST $ EL (SUC i) tr))
  ==> st.bst_fwdb = st'.bst_fwdb
Proof
  rpt strip_tac
  >> gvs[parstep_nice_def,parstep_cases,FLOOKUP_UPDATE,cstep_cases,clstep_cases]
  >- (
    qmatch_asmsub_rename_tac `EL (v_post - 1) (SND (EL i tr))`
    >> qpat_x_assum `!t. ~is_fulfil _ t _ _` $ qspec_then `v_post` assume_tac
    >> gvs[is_fulfil_def,FLOOKUP_UPDATE,bir_get_stmt_write,PRE_SUB1]
  )
  >- (
    qmatch_asmsub_rename_tac `EL (v_post - 1) (SND (EL i tr))`
    >> qpat_x_assum `!t. ~is_amo _ t _ _` $ qspec_then `v_post` assume_tac
    >> gvs[is_amo_def,FLOOKUP_UPDATE,bir_get_stmt_write,PRE_SUB1]
  )
  >- gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_get_stmt_branch,AllCaseEqs(),PRE_SUB1]
  >- (
    qmatch_assum_rename_tac `bir_get_stmt p _ = BirStmt_Generic stm`
    >> Cases_on `stm`
    >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_get_stmt_branch,AllCaseEqs(),pairTheory.ELIM_UNCURRY]
    >> TRY (
      qmatch_assum_rename_tac `bir_get_stmt p _ = BirStmt_Generic $ BStmtB b`
      >> Cases_on `b`
      >> gvs[bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,CaseEq"option",bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def,bir_programTheory.bir_state_is_terminated_def,bir_programTheory.bir_exec_stmtB_def,bir_get_stmt_generic]
      >> gvs[bir_programTheory.bir_exec_stmt_assert_def,bir_programTheory.bir_exec_stmt_assume_def,CaseEq"option",bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_observe_def]
      >> BasicProvers.every_case_tac
      >> gvs[]
    )
    >> qmatch_assum_rename_tac `bir_get_stmt p _ = BirStmt_Generic $ BStmtE e`
    >> Cases_on `e`
    >> fs[bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_exec_stmt_cjmp_def,bir_programTheory.bir_exec_stmt_halt_def]
    >> BasicProvers.every_case_tac
    >> gvs[bir_programTheory.bir_exec_stmt_assert_def,bir_programTheory.bir_exec_stmt_assume_def,CaseEq"option",bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_observe_def]
  )
QED

(* a positive fwdb at some location  l  comes from an earlier successful store
 * to this location *)

Theorem pos_fwdb_is_fulfil:
  !tr i cid p st st' t l.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ FLOOKUP (FST $ HD tr) cid = SOME $ Core cid p st'
  /\ st'.bst_fwdb l = <|fwdb_time := 0; fwdb_view := 0; fwdb_xcl := F|>
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ 0 < (st.bst_fwdb l).fwdb_time
  ==>
    ?j t st st'. j < i
    /\ is_fulfil cid t (EL j tr) (FST $ EL (SUC j) tr)
    /\ FLOOKUP (FST $ EL j tr) cid = SOME $ Core cid p st
    /\ FLOOKUP (FST $ EL (SUC j) tr) cid = SOME $ Core cid p st'
    /\ l = (EL (PRE t) $ SND $ EL j tr).loc
    /\ cid = (EL (PRE t) $ SND $ EL j tr).cid
    /\ st.bst_fwdb l <> st'.bst_fwdb l
    /\ same_state_prop_range cid tr (SUC j) i (λst. st.bst_fwdb l)
Proof
  rpt strip_tac
  >> qabbrev_tac `P = λj. ?k. k = i - j /\ 0 < j /\ j < i
    /\ is_fulfil cid t (EL k tr) (FST $ EL (SUC k) tr)
    /\ FLOOKUP (FST $ EL k tr) cid = SOME $ Core cid p st
    /\ FLOOKUP (FST $ EL (SUC k) tr) cid = SOME $ Core cid p st'
    /\ l = (EL (PRE t) $ SND $ EL k tr).loc
    /\ cid = (EL (PRE t) $ SND $ EL k tr).cid
    /\ st.bst_fwdb l <> st'.bst_fwdb l`
  >> reverse $ Cases_on `?i. P i`
  >- (
    fs[Abbr`P`,DISJ_EQ_IMP,AND_IMP_INTRO]
    >> `same_state_prop cid (FST $ HD tr) (FST $ EL i tr) (λst. st.bst_fwdb l)` by (
      cheat
    )
    >> gs[same_state_prop_def]
  )
  >> dxrule_then assume_tac arithmeticTheory.WOP
  >> gs[Abbr`P`,DISJ_EQ_IMP,AND_IMP_INTRO]
  >> qhdtm_assum `is_fulfil` $ irule_at Any
  >> fs[]
(* using
is_fulfil_xcl_bst_fwdb_eq
*)
  >> cheat
QED

Theorem is_read_xcl_timestamp_less_or_bst_xclb:
  !tr i j cid p st st' t.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_read_xcl cid t (EL i tr) (FST $ EL (SUC i) tr)
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  /\ FLOOKUP (FST $ EL (SUC i) tr) cid = SOME $ Core cid p st'
  ==> IS_SOME st'.bst_xclb /\ t <= (THE st'.bst_xclb).xclb_view
Proof
  rpt gen_tac >> strip_tac
  >> drule_at_then (Pat `is_read_xcl _ _ _ _`) assume_tac is_read_xcl_parstep_nice_eq
  >> Cases_on `0 < t`
  >> gvs[FLOOKUP_UPDATE,mem_read_view_def,mem_read_def]
  >> qmatch_asmsub_abbrev_tac `mem_read MM ll tt`
  >> qspecl_then [`tt`,`MM`,`ll`] assume_tac mem_read_EL_SND_loc
  >> gvs[optionTheory.IS_SOME_EXISTS,is_read_xcl_def]
  >> rpt disj2_tac
  >> IF_CASES_TAC
  >> fs[FLOOKUP_UPDATE]
  >> qhdtm_x_assum `is_certified` kall_tac
  >> qmatch_asmsub_abbrev_tac `_.bst_fwdb l`
  >> drule_then (drule_then $ qspec_then `0` assume_tac) wf_trace_cid_backward
  >> drule_at (Pat `FLOOKUP (FST $ EL i tr) _ = _`) pos_fwdb_is_fulfil
  >> gs[]
  >> disch_then $ qspec_then `l` mp_tac
  >> impl_tac
  >- fs[core_runs_spinlock_def,core_runs_prog_def,bir_programTheory.bir_state_init_def]
  (* there is no earlier store to location l in this thread *)
  (* the address location of the spinlock_var is never changed *)
  >> cheat
QED

(* a core in the critical section has run an earlier exclusive lr-sc pair *)

Theorem in_crit_lr_sc:
  !tr i cid p st st'.
  wf_trace tr /\ i < LENGTH tr
  /\ progressing_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST (EL i tr)) cid = SOME (Core cid p st)
  /\ in_crit (Core cid p st)
  ==> ?t1 i1 t2 i2. lr_sc cid tr t1 i1 t2 i2 /\ i2 < i
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac in_crit_is_fulfil_xcl
  >> fs[lr_sc_def]
  >> qhdtm_assum `is_fulfil_xcl` $ irule_at Any
  >> drule_all_then strip_assume_tac wf_trace_cid_backward'
  >> drule_at_then (Pat `is_fulfil_xcl _ _ _ _`) assume_tac is_fulfil_xcl_is_read_xcl
  >> imp_res_tac is_fulfil_xcl_is_fulfil
  >> drule_at_then (Pat `is_fulfil _ _ _ _`) assume_tac is_fulfil_to_memory
  >> gs[]
  >> qhdtm_assum `is_read_xcl` $ irule_at Any
  >> fs[]
  >> conj_asm1_tac
  >- (
    drule_at_then (Pat `is_fulfil_xcl _ _ _ _`) assume_tac is_fulfil_xcl_bst_xclb_less_timestamp
    >> drule_at (Pat `FLOOKUP _ _ = _`) wf_trace_cid_backward
    >> qmatch_assum_rename_tac `j' < j`
    >> disch_then (fn thm =>
      qspec_then `j'` assume_tac thm
      >> qspec_then `SUC j'` assume_tac thm)
    >> drule_at_then (Pat `is_read_xcl _ _ _ _`) assume_tac is_read_xcl_timestamp_less_or_bst_xclb
    >> gs[]
    >> first_x_assum $ drule_at_then Any assume_tac
    >> gs[]
  )
  >> conj_tac
  >- (
    fs[same_state_prop_range_def]
    (* by induction *)
    >> cheat
  )
  (* a property of the spinlock program *)
  >> cheat
QED

Theorem init_unique:
  !i tr. wf_trace tr /\ wf_trace1 tr
  /\ progressing_trace tr
  /\ SUC i < LENGTH tr
  /\ cores_run_spinlock $ FST $ HD tr
  /\ invariant (FST $ EL i tr)
  ==> invariant (FST $ EL (SUC i) tr)
Proof
  rw[invariant_def]
  >> imp_res_tac cores_run_spinlock_init
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> imp_res_tac parstep_nice_EX_FLOOKUP
  >> drule_all_then strip_assume_tac parstep_nice_FLOOKUP
  >> drule_all_then assume_tac wf_trace_core_runs_spinlock_FLOOKUP'
  >> Cases_on `st.bst_pc = st'.bst_pc`
  >- (
    fs[unique_def,in_crit_def,parstep_nice_def,parstep_cases]
    >> rw[FLOOKUP_UPDATE,DISJ_EQ_IMP]
    >> spose_not_then assume_tac
    >> gvs[FLOOKUP_UPDATE]
    >> first_x_assum $ dxrule_at $ Pat `FLOOKUP _ _ = _`
    >> disch_then $ dxrule_at $ Pat `FLOOKUP _ _ = _`
    >> fs[in_crit_def]
  )
  >> rev_drule_all_then assume_tac reachable_pc_sl_step
  >> reverse $ Cases_on `in_crit $ THE $ FLOOKUP (FST $ EL (SUC i) tr) cid`
  >- (
    Q.ISPEC_THEN `in_crit` rev_drule FLOOKUP_NOT_unique_eq
    >> disch_then $ drule_at Any
    >> gvs[optionTheory.option_CLAUSES,parstep_nice_def,parstep_cases,FLOOKUP_UPDATE]
    >> disch_then irule
    >> drule_then (drule_at Any) in_crit_sl_step
    >> fs[]
  )
  >> gvs[sl_step_cases,bst_pc_tuple_def,in_crit_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> reverse $ Cases_on `
    ?cid p st. FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
    /\ in_crit $ Core cid p st
    `
  >- (
    rw[unique_def,FLOOKUP_UPDATE]
    >> spose_not_then assume_tac
    >> fs[DISJ_EQ_IMP]
    >> qmatch_assum_rename_tac `FLOOKUP _ id' = SOME $ xx` >> Cases_on `xx`
    >> qmatch_assum_rename_tac `FLOOKUP _ id = SOME $ xx` >> Cases_on `xx`
    >> drule_then imp_res_tac wf_trace1_FLOOKUP
    >> gvs[]
    >> drule_at Any wf_trace_cid_backward1
    >> qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac
    >> drule_at Any wf_trace_cid_backward1
    >> rpt strip_tac
    >> gvs[]
    >> PRED_ASSUM is_forall imp_res_tac
    >> `id <> cid /\ id' <> cid` by (
      conj_tac
      >> spose_not_then assume_tac
      >> gvs[]
      >> rev_dxrule_at (Pat $ `FLOOKUP _ _ = _`) wf_trace_unchanged
      >> disch_then $ dxrule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
      >> gvs[]
      >> gs[bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality,in_crit_def]
    )
    >> Cases_on `parstep_nice id (EL i tr) (EL (SUC i) tr)`
    >- imp_res_tac progressing_trace_cid_eq
    >> Cases_on `parstep_nice id' (EL i tr) (EL (SUC i) tr)`
    >- imp_res_tac progressing_trace_cid_eq
    >> ntac 2 $ dxrule_at (Pat `~parstep_nice _ _ _`) wf_trace_NOT_parstep_nice_state_EQ'
    >> rpt strip_tac
    >> rfs[]
    >> gvs[]
  )
  >> fs[]
  >> `cid <> cid'` by (
    spose_not_then assume_tac
    >> gvs[in_crit_def]
  )
  >> drule_all_then assume_tac progressing_trace_state'
  >> spose_not_then kall_tac
  >> `core_runs_spinlock cid (FST $ HD tr)
    /\ core_runs_spinlock cid' (FST $ HD tr)` by (
    drule_at (Pat `FLOOKUP _ _ = _`) wf_trace_cid_backward'
    >> disch_then $ qspec_then `0` assume_tac
    >> gs[cores_run_spinlock_def]
  )
  >> `in_crit $ Core cid p st'` by fs[in_crit_def,bst_pc_tuple_def,bir_programTheory.bir_programcounter_t_component_equality]
  >> ntac 2 $ dxrule_at_then (Pat`core_runs_spinlock cid _`) (qspec_then `SUC i` assume_tac) in_crit_lr_sc
  >> gs[]
  >> qmatch_assum_rename_tac `lr_sc cid tr t1 i1 t2 i2`
  >> qmatch_assum_rename_tac `lr_sc cid' tr t1' i1' t2' i2'`
(*
TODO resolve all interleavings
lr_sc_interleaved_pair
*)
  >> cheat
QED

val _ = export_theory();
