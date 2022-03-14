
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
  /\ init (FST $ HD tr)
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
  >> gvs[FLOOKUP_UPDATE]
  >> fs $ map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
    [bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Fence,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,
    bir_get_stmt_bir_spinlock_prog_BirStmt_None,
    bir_get_stmt_bir_spinlock_prog_BirStmt_Expr]
  >> gvs[bir_programTheory.bir_pc_next_def,AllCaseEqs(),bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_None,bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,bir_programTheory.bir_exec_stmt_cjmp_def,bst_pc_tuple_def,reachable_pc_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_programTheory.bir_pc_next_def,AllCaseEqs(),bir_get_stmt_bir_spinlock_prog_BirStmt_Write_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Read_EQ,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_Generic,bir_get_stmt_bir_spinlock_prog_BirStmt_Expr,bir_get_stmt_bir_spinlock_prog_BirStmt_None,bir_get_stmt_bir_spinlock_prog_BirStmt_Branch,bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_bin_pred_def,bir_expTheory.bir_eval_bin_exp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_block_pc_def,get_fulfil_args_def,get_read_args_def]
QED

Theorem wf_trace_reachable_pc:
  !i tr cid p st. wf_trace tr
  /\ i < LENGTH tr
  /\ init (FST $ HD tr)
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ FLOOKUP (FST $ EL i tr) cid = SOME $ Core cid p st
  ==> reachable_pc st.bst_pc
Proof
  Induct
  >> rpt strip_tac
  >- (
    fs[init_def]
    >> res_tac
    >> fs[bst_pc_tuple_def,reachable_pc_def]
  )
  >> drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> first_x_assum $ drule_at_then (Pat `FLOOKUP _ _ = _`) assume_tac
  >> gs[]
  >> drule_all_then assume_tac reachable_pc_sim
  >> dxrule_all reachable_pc_sl_step_imp
  >> fs[]
QED

Theorem reachable_pc_sl_step:
  !i tr cid p st st'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ init (FST $ HD tr)
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

Definition invariant_def:
  invariant cores = unique cores in_crit
End

Theorem init_unique_in_crit_imp:
  !i tr. wf_trace tr /\ wf_trace1 tr
  /\ init (FST $ HD tr)
  ==> invariant (FST $ HD tr)
Proof
  rw[init_def,invariant_def,unique_def,Excl"EL",GSYM EL,Excl"EL_restricted"]
  >> drule_then drule wf_trace1_FLOOKUP
  >> drule_then rev_drule wf_trace1_FLOOKUP
  >> rw[wf_trace_NOT_NULL,LENGTH_NOT_NULL]
  >> fs[in_crit_def]
  >> qpat_x_assum `!cid p st. FLOOKUP _ _ = _ ==> _` imp_res_tac
  >> gs[]
QED

Definition same_state_def:
  same_state cid st1 st2 =
    !p st.
      FLOOKUP st1 cid = SOME $ Core cid p st
      /\ FLOOKUP st2 cid = SOME $ Core cid p st
End

Theorem init_unique:
  !i tr. wf_trace tr /\ wf_trace1 tr
  /\ SUC i < LENGTH tr
  /\ cores_run_spinlock $ FST $ HD tr
  /\ init (FST $ HD tr)
  /\ invariant (FST $ EL i tr)
  ==> invariant (FST $ EL (SUC i) tr)
Proof
  rw[invariant_def]
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
      >> disch_then $ dxrule_at_then (Pat $ `FLOOKUP _ _ = _`) assume_tac
      >> gvs[]
      >> gs[bir_programTheory.bir_state_t_component_equality,bir_programTheory.bir_programcounter_t_component_equality,in_crit_def]
    )
    >> Cases_on `parstep_nice id (EL i tr) (EL (SUC i) tr)`
    >- imp_res_tac parstep_nice_parstep_nice
    >> Cases_on `parstep_nice id' (EL i tr) (EL (SUC i) tr)`
    >- imp_res_tac parstep_nice_parstep_nice
    >> ntac 2 $ dxrule_at (Pat `~parstep_nice _ _ _`) wf_trace_NOT_parstep_nice_state_EQ'
    >> rpt strip_tac
    >> rfs[]
    >> gvs[]
  )
  >> fs[]
  >> cheat
QED

val _ = export_theory();
