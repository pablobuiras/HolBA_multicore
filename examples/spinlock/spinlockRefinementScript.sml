
open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
(* open tracesTheory tracestepTheory spinlockTheory ; *)

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
(* TODO place elsewhere *)

(* adjusted parstep_nice definition *)

Definition parstep_nice_def:
  parstep_nice cid s1 s2
  = parstep cid (FST s1) (SND s1) (FST s2) (SND s2)
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

(*****************************************************************************)
(* Extracting reachable states of a program **********************************)
(*****************************************************************************)
(* TODO some theorems need further adjustement *)

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Generic =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Generic stm``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [BETA_THM]
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

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_Amo =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_Amo var a_e v_e acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs()]

Theorem bir_get_stmt_bir_spinlockfull_prog_BirStmt_None =
  EVAL ``bir_get_stmt bir_spinlockfull_prog x = BirStmt_None``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) [AC CONJ_ASSOC CONJ_COMM]
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Read =
  EVAL ``bir_get_stmt bir_spinlockfull_prog pc = BirStmt_Read var a_e opt_cast xcl acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_bir_spinlock_prog_BirStmt_Write =
  EVAL ``bir_get_stmt bir_spinlockfull_prog pc = BirStmt_Write a_e v_e xcl acq rel``
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

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

(*****************************************************************************)
(* Spinlock specification ****************************************************)
(*****************************************************************************)

(* returns the word with the cid's bit set to 1
0...010...0
     ^
    cid
*)
(* TODO define *)

Definition cid2w_def:
  cid2w (cid : num) = BExp_Const $ Imm64 (ARB : word64)
End

(* For the initial state we assume a_spinlock_init g_eng
 * which says: _GHOST.crit contains initially only zeros (= lock is free) *)

Definition a_spinlock_init_def:
  a_spinlock_init g_env <=>
    bir_eval_exp (BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                    (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
                    BEnd_LittleEndian Bit32) g_env
    = SOME $ BVal_Imm $ Imm64 0w
End

(* Abstract spinlock specification that is parametrised by its core id.
 * The core id is used to mark the lock as taken. *)
(* TODO Requires a limited number of threads. *)

Definition a_spinlock_def:
  a_spinlock cid =
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

(* all possible steps of the abstract spinlock
 * sl_step (block,pc) (block',pc') *)
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

(* the spinlock refinement relation between abstract state aS
 * and concrete state S for a core id cid *)
Definition slrefinerel_def:
  slrefinerel cid aS S =
  (!cores M g_env acores aM ag_env.
       cores = FST S
    /\ M = FST $ SND S
    /\ g_env = SND $ SND S
    /\ acores = FST aS
    /\ aM = FST $ SND aS
    /\ ag_env = SND $ SND aS
    ==>
    (* we only reason about reachable states *)
       reachable_sl ((core_state cid aS).bst_pc)
    /\ reachable_slf ((core_state cid S).bst_pc)
    /\ core_prog cid aS = bir_spinlock cid
    /\ core_prog cid S = bir_spinlockfull_prog
    /\ aM = M
    (* TODO extend *)
  )
End

(* refinement theorem *)
(* the abstract state is prefixed with "a" *)

Theorem spinlock_refinement:
  !cid S S' aS aS'.
  parstep_nice cid S S'
  /\ slrefinerel cid aS S
  ==>
    slrefinerel cid aS S'
    \/ ?aS'. gstep cid aS aS'
          /\ slrefinerel cid aS' S'
Proof
  cheat
QED

val _ = export_theory();
