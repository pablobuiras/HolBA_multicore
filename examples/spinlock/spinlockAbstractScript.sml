open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
open spinlockConcreteTheory ;

(* TODO currently some general definitions are in spinlockConcreteTheory *)
val _ = new_theory "spinlockAbstract";

(*****************************************************************************)
(* Spinlock specification ****************************************************)
(*****************************************************************************)

(* Abstract spinlock specification that is parametrised by its core id.
 * The core id is used to mark the lock as taken. *)

Definition spinlock_aprog_def:
  spinlock_aprog cid dummy_loc =
  BirProgram [
  (* lock block *)
  <|bb_label := BL_Address_HC (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [
        BStmt_Assign (BVar "_is_locked" $ BType_Imm Bit64)
          (* BExp_Load mem_e a_e endianness type *)
            $ BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                      (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
                      BEnd_LittleEndian Bit32;
        (* note core id in critical section *)
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit_cid" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_IfThenElse
                (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
                (BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                      (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
                      BEnd_LittleEndian Bit32)
                (BExp_Const $ Imm64 cid);
        (* lock if possible *)
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_IfThenElse
                (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
                (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
                (BExp_Const $ Imm64 1w);
      ];
    (* spin on _is_locked *)
    bb_last_statement :=
        BStmt_CJmp
          (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
          (BLE_Label $ BL_Address $ Imm64 0w)
          (BLE_Label $ BL_Address $ Imm64 4w);
  |>;

  (* load reserved on fresh dummy variable *)

  <|bb_label := BL_Address_HC (Imm64 4w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := T; mc_rel := F|>;
    bb_statements :=
      [BStmt_Assert
          $ BExp_Aligned Bit64 2 $ BExp_Den $ BVar dummy_loc $ BType_Imm Bit64;
        BStmt_Assign (BVar "_ignore" (BType_Imm Bit64))
          $ BExp_Cast BIExp_SignedCast
            (BExp_Load (BExp_Den $ BVar "MEM8" $ BType_Mem Bit64 Bit8)
                (BExp_Den $ BVar dummy_loc $ BType_Imm Bit64)
                BEnd_LittleEndian Bit32) Bit64;
        BStmt_Assign (BVar "MEM8_R" $ BType_Mem Bit64 Bit8)
          $ BExp_Store (BExp_Den $ BVar "MEM8_Z" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar dummy_loc $ BType_Imm Bit64) BEnd_LittleEndian
            $ BExp_Const $ Imm32 1w];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;

  (* unlock *)
  <|bb_label := BL_Address_HC (Imm64 8w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [
      (* free reset *)
      BStmt_Assign
        (BVar "_GHOST" $ BType_Mem Bit64 Bit8)
        $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
          (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
          BEnd_LittleEndian
          $ BExp_Const $ Imm64 0w;
      ];
    bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 12w
  |>;

  (* store conditional on dummy variable *)
  <|bb_label := BL_Address_HC (Imm64 12w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [BStmt_Assert
          (BExp_Aligned Bit64 2 $ BExp_Den $ BVar dummy_loc $ BType_Imm Bit64);
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
            (BExp_Den (BVar dummy_loc $ BType_Imm Bit64)) 4);
        BStmt_Assign (BVar "MEM8" (BType_Mem Bit64 Bit8))
          (BExp_IfThenElse
            (BExp_BinPred BIExp_Equal
                (BExp_Load
                  (BExp_Den $ BVar "MEM8_R" $ BType_Mem Bit64 Bit8)
                  (BExp_Den $ BVar dummy_loc $ BType_Imm Bit64)
                  BEnd_LittleEndian Bit64)
                (BExp_Const $ Imm32 0x1010101w))
            (BExp_Store (BExp_Den $ BVar "MEM8" $ BType_Mem Bit64 Bit8)
                (BExp_Den $ BVar dummy_loc $ BType_Imm Bit64)
                BEnd_LittleEndian
                (BExp_Cast BIExp_LowCast
                  (BExp_Den $ BVar "_ignore" $ BType_Imm Bit64) Bit32))
            (BExp_Den $ BVar "MEM8" $ BType_Mem Bit64 Bit8));
        BStmt_Assign (BVar "_ignore" (BType_Imm Bit64))
          (BExp_IfThenElse
            (BExp_BinPred BIExp_Equal
                (BExp_Load
                  (BExp_Den (BVar "MEM8_R" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar dummy_loc (BType_Imm Bit64)))
                  BEnd_LittleEndian Bit64)
                (BExp_Const (Imm32 0x1010101w))) (BExp_Const (Imm64 0w))
            (BExp_Const (Imm64 0x101010101010101w)));
        BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
          (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;

  ] : string bir_program_t
End

(* lookup _GHOST.crit to contain only zeros (= lock is free) *)
(* TODO assume for initial state *)

Definition is_free_asl_def:
  is_free_asl g_env <=>
    bir_read_mem_var "_GHOST" "crit" g_env = SOME $ BVal_Imm $ Imm64 0w
End

(*****************************************************************************)
(* Extracting reachable states of a program **********************************)
(*****************************************************************************)
(* TODO some theorems need further adjustement *)

Theorem bir_get_stmt_spinlock_aprog_BirStmt_Generic =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_Generic stm``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_spinlock_aprog_BirStmt_Fence =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_Fence mo1 mo2``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_spinlock_aprog_BirStmt_Branch =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_Branch a1 a2 a3``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_spinlock_aprog_BirStmt_Expr =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_Expr var e``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> CONV_RULE $ ONCE_DEPTH_CONV $ RHS_CONV $ computeLib.EVAL_CONV
  |> GEN_ALL

(*
Theorem bir_get_stmt_spinlock_aprog_BirStmt_Amo =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_Amo var a_e v_e acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs()]
  |> GEN_ALL
*)

Theorem bir_get_stmt_spinlock_aprog_BirStmt_Amo:
  !x cid var a_e v_e acq rel.
  bir_get_stmt (spinlock_aprog cid) x = BirStmt_Amo var a_e v_e acq rel ==> F
Proof
  cheat
QED

Theorem bir_get_stmt_spinlock_aprog_BirStmt_None =
  EVAL ``bir_get_stmt (spinlock_aprog cid) x = BirStmt_None``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [AC CONJ_ASSOC CONJ_COMM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [get_read_args_def,get_fulfil_args_def]
  |> GEN_ALL

(* TODO calculate is_rel_def,is_amo_def,is_xcl_read_def,is_acq_def *)
Theorem bir_get_stmt_spinlock_aprog_BirStmt_Read =
  REFL ``bir_get_stmt (spinlock_aprog cid) pc = BirStmt_Read var a_e opt_cast xcl acq rel``
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ REWRITE_CONV [bir_get_stmt_write,bir_get_stmt_read]
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ ONCE_DEPTH_CONV $ REWRITE_CONV [Once spinlock_aprog_def]
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
Theorem bir_get_stmt_spinlock_aprog_BirStmt_Write =
  REFL ``bir_get_stmt (spinlock_aprog cid) pc = BirStmt_Write a_e v_e xcl acq rel``
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ REWRITE_CONV [bir_get_stmt_write,bir_get_stmt_read]
  |> CONV_RULE $ DEPTH_CONV $ RHS_CONV $ ONCE_DEPTH_CONV $ REWRITE_CONV [Once spinlock_aprog_def]
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

Theorem bir_get_stmt_spinlock_aprog_thms =
  LIST_CONJ $
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
    [bir_get_stmt_spinlock_aprog_BirStmt_Generic,
    bir_get_stmt_spinlock_aprog_BirStmt_Fence,
    bir_get_stmt_spinlock_aprog_BirStmt_Branch,
    bir_get_stmt_spinlock_aprog_BirStmt_Expr,
    bir_get_stmt_spinlock_aprog_BirStmt_None,
    bir_get_stmt_spinlock_aprog_BirStmt_Amo,
    bir_get_stmt_spinlock_aprog_BirStmt_Write,
    bir_get_stmt_spinlock_aprog_BirStmt_Read]

Theorem bir_spinlock_aprog_is_xcl_write1:
  !cid pc. pc.bpc_label = BL_Address (Imm64 0w) /\ pc.bpc_index = 2
  ==>
    ~is_xcl_read (spinlock_aprog cid) pc
      (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
Proof
  rpt gen_tac >> strip_tac
  >> EVAL_TAC
  >> fs[]
QED

Theorem bir_spinlock_aprog_is_xcl_write2:
  !cid pc. pc.bpc_label = BL_Address (Imm64 4w) /\ pc.bpc_index = 0
  ==>
    ~is_xcl_read (spinlock_aprog cid) pc
      (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
Proof
  rpt gen_tac >> strip_tac
  >> EVAL_TAC
  >> fs[]
QED

(* all possible steps of the abstract spinlock
 * sl_step (block,pc) (block',pc') *)
(* TODO rename control flow *)
(* TODO automate *)

Inductive asl_step:
     asl_step (BL_Address $ Imm64 0w,0n) (BL_Address $ Imm64 0w,1n)
  /\ asl_step (BL_Address $ Imm64 0w,1)  (BL_Address $ Imm64 0w,2)
  /\ asl_step (BL_Address $ Imm64 0w,2)  (BL_Address $ Imm64 0w,3)
  /\ asl_step (BL_Address $ Imm64 0w,3)  (BL_Address $ Imm64 0w,0)
  /\ asl_step (BL_Address $ Imm64 0w,3)  (BL_Address $ Imm64 4w,0)
  /\ asl_step (BL_Address $ Imm64 4w,0)  (BL_Address $ Imm64 4w,1)
  /\ asl_step (BL_Address $ Imm64 4w,1)  (BL_Address $ Imm64 8w,1)
End

(* pc is reachable for bir_spinlock from its first pc *)
(* TODO automate *)

Definition reachable_asl_def:
  reachable_asl pc =
    !bpt. bpt = bst_pc_tuple pc ==>
    bpt = (BL_Address $ Imm64 0w,0) \/ bpt = (BL_Address $ Imm64 0w,1) \/
    bpt = (BL_Address $ Imm64 0w,2) \/ bpt = (BL_Address $ Imm64 0w,3) \/
    bpt = (BL_Address $ Imm64 4w,0) \/ bpt = (BL_Address $ Imm64 8w,0)
End


(* pc within crit region *)
(* the abstract program contains only one statement, thus behaves atomically *)
Definition in_crit_asl_def:
  in_crit_asl pc <=> reachable_asl pc
    /\ !bpt. bpt = bst_pc_tuple pc ==>
      bpt = (BL_Address $ Imm64 4w,0)
End

(* pc within lock region *)
Definition in_lock_asl_def:
  in_lock_asl pc <=>
    reachable_asl pc
    /\ !n. bst_pc_tuple pc = (BL_Address $ Imm64 0w,n) ==> 0 < n
End

(* pc within lock region *)
Definition in_unlock_asl_def:
  in_unlock_asl pc <=>
    reachable_asl pc
    /\ !n. bst_pc_tuple pc = (BL_Address $ Imm64 4w,n) ==> 0 < n
End

(* pc not in lock or unlock region *)
(*
Definition outside_un_lock_asl_def:
  outside_un_lock_asl pc <=>
    !x n. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
    ==>  (x,n) = (0w,0)
      \/ (x,n) = (4w,0)
      \/ (x,n) = (8w,0)
End
*)

val _ = export_theory();
