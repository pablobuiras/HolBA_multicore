
open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory
(* tracestepTheory spinlockTheory ; *)

val _ = new_theory "spinlockRefinement";

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

(* compare address range *)

Definition bir_laImm64_lt_def:
  bir_laImm64_lt a w =
    case a of
    | BL_Address (Imm64 v) => v < w
    | _ => F
End

Definition bir_laImm64_lt2_def:
  bir_laImm64_lt2 w a =
    case a of
    | BL_Address (Imm64 v) => w < v
    | _ => F
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

(* all possible steps of the full spinlock
 * sl_step (block,pc) (block',pc') *)
(* TODO automate *)

Inductive slf_step:
     slf_step (BL_Address $ Imm64 0w,0n) (BL_Address $ Imm64 4w,0n)
  /\ slf_step (BL_Address $ Imm64 4w,0)  (BL_Address $ Imm64 8w,0)
  /\ slf_step (BL_Address $ Imm64 8w,0)  (BL_Address $ Imm64 4w,0)
  /\ slf_step (BL_Address $ Imm64 8w,0)  (BL_Address $ Imm64 12w,0)
  /\ slf_step (BL_Address $ Imm64 12w,0) (BL_Address $ Imm64 16w,0)
  /\ slf_step (BL_Address $ Imm64 16w,0) (BL_Address $ Imm64 20w,0)
  /\ slf_step (BL_Address $ Imm64 20w,0) (BL_Address $ Imm64 4w,0)
  /\ slf_step (BL_Address $ Imm64 20w,0) (BL_Address $ Imm64 24w,0)
  /\ slf_step (BL_Address $ Imm64 24w,0) (BL_Address $ Imm64 28w,0)
  /\ slf_step (BL_Address $ Imm64 28w,0) (BL_Address $ Imm64 32w,0)
  /\ slf_step (BL_Address $ Imm64 32w,0) (BL_Address $ Imm64 36w,0)
  /\ slf_step (BL_Address $ Imm64 36w,0) (BL_Address $ Imm64 40w,0)
End

(* pc is reachable for bir_spinlockfull_prog from its first pc *)
(* TODO automate *)

Definition reachable_slf_def:
  reachable_slf pc =
    !bpt. bpt = bst_pc_tuple pc ==>
         bpt = (BL_Address $ Imm64 0w,0n) \/ bpt = (BL_Address $ Imm64 4w,0)
      \/ bpt = (BL_Address $ Imm64 8w,0)  \/ bpt = (BL_Address $ Imm64 12w,0)
      \/ bpt = (BL_Address $ Imm64 16w,0) \/ bpt = (BL_Address $ Imm64 20w,0)
      \/ bpt = (BL_Address $ Imm64 24w,0) \/ bpt = (BL_Address $ Imm64 28w,0)
      \/ bpt = (BL_Address $ Imm64 32w,0) \/ bpt = (BL_Address $ Imm64 36w,0)
      \/ bpt = (BL_Address $ Imm64 40w,0)
End

(* pc within crit region *)

Definition in_crit_slf_def:
  in_crit_slf pc <=>
    reachable_asl pc /\ bst_pc_tuple pc = (BL_Address $ Imm64 32w,0)
End

(* pc not in lock or unlock region *)
Definition outside_un_lock_slf_def:
  outside_un_lock_slf pc <=>
    !x n. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
    ==>  (x,n) = (0w,0)
      \/ (24w <= x /\ x <= 36w)
      \/ x = 40w
End

(* thread  cid  sees a free lock *)

Definition is_free_slf_def:
  is_free_slf cid S <=>
    bir_read_mem_var "MEM8" "x7" ((core_state cid S).bst_environ)
    = SOME $ BVal_Imm $ Imm64 0w
End

(*****************************************************************************)
(* Spinlock specification ****************************************************)
(*****************************************************************************)

(* returns the word with the cid's bit set to 1
0...010...0 : word64
     ^
    cid

requires cid < 64 *)

Definition cid2w_def:
  cid2w (cid : num) =
    (* left shift of 1 by cid *)
    BExp_BinExp BIExp_LeftShift (BExp_Const $ Imm64 1w) (BExp_Const $ Imm64 $ (n2w cid) :word64)
End

(* Abstract spinlock specification that is parametrised by its core id.
 * The core id is used to mark the lock as taken.
 * Requires a limited number of threads (inherited by cid2w) *)

Definition spinlock_aprog_def:
  spinlock_aprog cid =
  BirProgram [
  (* lock block *)
  <|bb_label := BL_Address_HC (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [
        (* _tmp := _GHOST.crit *)
        BStmt_Assign (BVar "_tmp" $ BType_Imm Bit64)
          (* BExp_Load mem_e a_e endianness type *)
            $ BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                      (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
                      BEnd_LittleEndian Bit32;
        (* _is_locked := (_tmp != 0) *)
        BStmt_Assign (BVar "_is_locked" $ BType_Imm Bit64)
          $ BExp_IfThenElse
              (BExp_BinExp BIExp_And
                (BExp_Const $ Imm64 0w)
                (BExp_Den $ BVar "_tmp" $ BType_Imm Bit64))
              (BExp_Const $ Imm64 1w)
              (BExp_Const $ Imm64 0w);
        (* lock if possible *)
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_IfThenElse
                (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
                (BExp_Den $ BVar "_tmp" $ BType_Imm Bit64)
                (cid2w cid);
      ];
    (* spin on _is_locked *)
    bb_last_statement :=
        BStmt_CJmp
          (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64)
          (BLE_Label $ BL_Address $ Imm64 0w)
          (BLE_Label $ BL_Address $ Imm64 4w);
  |>;
  (* unlock *)
  <|bb_label := BL_Address_HC (Imm64 4w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [
(*
reset lock availability for cid by writing
_GHOST.crit := (1...101...1   AND   _GHOST.crit)
                     ^
                    cid
*)
      BStmt_Assign
        (BVar "_GHOST" $ BType_Mem Bit64 Bit8)
        $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
          (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
          BEnd_LittleEndian
          $ BExp_BinExp BIExp_And
              (BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
                BEnd_LittleEndian Bit32)
              $ BExp_UnaryExp BIExp_Not $ cid2w cid;
      ];
    bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 8w
  |>
  ] : string bir_program_t
End

(* lookup _GHOST.crit to contain only zeros (= lock is free) *)
(* TODO assume for initial state *)

Definition is_free_asl_def:
  is_free_asl g_env <=>
    bir_read_mem_var "_GHOST" "crit" g_env = SOME $ BVal_Imm $ Imm64 0w
End

(* all possible steps of the abstract spinlock
 * sl_step (block,pc) (block',pc') *)
(* TODO rename control flow *)
(* TODO automate *)

Inductive asl_step:
     asl_step (BL_Address $ Imm64 0w,0n) (BL_Address $ Imm64 0w,1n)
  /\ asl_step (BL_Address $ Imm64 0w,1)  (BL_Address $ Imm64 0w,2)
  /\ asl_step (BL_Address $ Imm64 0w,2)  (BL_Address $ Imm64 0w,0)
  /\ asl_step (BL_Address $ Imm64 0w,2)  (BL_Address $ Imm64 4w,0)
  /\ asl_step (BL_Address $ Imm64 4w,0)  (BL_Address $ Imm64 8w,0)
End

(* pc is reachable for bir_spinlock from its first pc *)
(* TODO automate *)

Definition reachable_asl_def:
  reachable_asl pc =
    !bpt. bpt = bst_pc_tuple pc ==>
    bpt = (BL_Address $ Imm64 0w,0) \/ bpt = (BL_Address $ Imm64 0w,1) \/
    bpt = (BL_Address $ Imm64 0w,2) \/ bpt = (BL_Address $ Imm64 4w,0) \/
    bpt = (BL_Address $ Imm64 8w,0)
End

(* pc within crit region *)
(* the abstract program contains only one statement, thus behaves atomically *)
Definition in_crit_asl_def:
  in_crit_asl pc <=> reachable_asl pc
End

(* pc not in lock or unlock region *)
Definition outside_un_lock_asl_def:
  outside_un_lock_asl pc <=>
    !x n. bst_pc_tuple pc = (BL_Address $ Imm64 x,n)
    ==>  (x,n) = (0w,0)
      \/ (x,n) = (4w,0)
      \/ (x,n) = (8w,0)
End

(* TODO define statement *)
Definition same_pc_als_slf_def:
  same_pc_als_slf pc pc' <=>
    (ARB :bool)
End

(* the spinlock refinement relation between abstract state aS
 * and concrete state S for a core id cid *)
(* TODO parametrise over projection of aS and S at cid *)
Definition asl_slf_rel_def:
  asl_slf_rel cid aS S =
  (!cores M acores aM agenv genv.
       cores = FST S
    /\ M = FST $ SND S
    /\ genv = SND $ SND S
    /\ acores = FST aS
    /\ aM = FST $ SND aS
    /\ agenv = SND $ SND aS
    ==>
    (* we only reason about reachable states *)
       reachable_asl (core_pc cid aS)
    /\ reachable_slf (core_pc cid S)
    /\ core_prog cid aS = spinlock_aprog cid
    /\ core_prog cid S = bir_spinlockfull_prog
    (* lock is free *)
    /\ is_free_slf cid S = is_free_asl agenv
    (* pc outside lock and unlock *)
    /\ (
      outside_un_lock_asl (core_pc cid aS)
      /\ outside_un_lock_slf (core_pc cid S)
      ==> same_pc_als_slf (core_pc cid aS) (core_pc cid S)
    )
    (* not taking the lock *)
    /\ (
      (bir_laImm64_lt (FST $ bst_pc_tuple $ core_pc cid S) 20w
      /\ (FST $ bst_pc_tuple $ core_pc cid S = BL_Address $ Imm64 20w ==>
          bir_read_core_reg_zero "x6" cid S) (* unsuccessful store *)
      ) ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 0w,0)
    )
    (* future successful store *)
    /\ (
        FST $ bst_pc_tuple $ core_pc cid S = BL_Address $ Imm64 20w
        /\ ~bir_read_core_reg_zero "x6" cid S
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* successful store *)
    /\ (
        FST $ bst_pc_tuple $ core_pc cid S = BL_Address $ Imm64 24w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after lock, before unlock *)
    /\ (
        bir_laImm64_lt2 24w (FST $ bst_pc_tuple $ core_pc cid S)
        /\ bir_laImm64_lt (FST $ bst_pc_tuple $ core_pc cid S) 40w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
        FST $ bst_pc_tuple $ core_pc cid S = BL_Address $ Imm64 40w
        ==> bst_pc_tuple $ core_pc cid aS = (BL_Address $ Imm64 8w,0)
    )
  )
End

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
  cheat
QED

val _ = export_theory();

