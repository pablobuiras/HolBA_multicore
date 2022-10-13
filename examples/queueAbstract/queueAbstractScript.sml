(* UNFINISHED *)

open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
open spinlockConcreteTheory ;
val _ = new_theory "queueAbstract";

(*****************************************************************************)
(* Abstract queue specification **********************************************)
(*****************************************************************************)
(* Would have preferred an abstract supersimple sequential queue             *)
(* But need to fit into bounded (64 bit) model memory                        *)
(* So instead specify a bounded circular queue                               *)
(* Due to Bir limitations                                                    *)
(* Pre:                                                                      *)
(* Post:                                                                     *)
(* Memory variables:                                                         *)
(*  - _hd: Queue head location                                               *)
(*  - _tl: Queue tail location                                               *)
(*  - _qmax: Max queue address                                               *)
(*  - _qmin: Min queue address                                               *)
(* TO BE COMPLETED                                                           *)

Definition enq_aprog_def:
  enq_aprog cid hd tl =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        BEnqueue_aprog (BExp_Den $ BVar "_cid" $ BType_Imm Bit32)
          (BExp_Den $ BVar "_tl" $ BType_Imm Bit64)
          BEnd_LittleEndian Bit32 ;
        (* enq(cid,tl)                           *)
        (* BEnqueue is a macro, as yet undefined *)
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
  <|bb_label := BL_Address (Imm64 4w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
        BStmt_Assign (BVar "_nxt" $ BType_Imm Bit32)
          $ BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                      (BExp_Den $ BVar "_hd" $ BType_Imm Bit64)
                      BEnd_LittleEndian Bit32;
        (* nxt = hd(q) *)
        BStmt_Assign (BVar "_branch" $ BType_Imm Bit8)
                     (BExp_BinExp BIExp_Minus
                       (BExp_Den $ BVar "_nxt" $ BType_Imm Bit32)
                       (BExp_Den $ BVar "_cid" $ BType_Imm Bit32)) ;
      ];
    bb_last_statement :=
      BStmt_CJmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
  <|bb_label := BL_Address (Imm64 4w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_Const $ Imm64 1w ;
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))
  |> ;
] ;

Definition fifo_unlock_aprog_def:
  fifo_unlock_aprog cid hd tl =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_Const $ Imm64 0w ;
        BDequeue_aprog (BExp_Den $ BVar "_cid" $ BType_Imm Bit32)
          (BExp_Den $ BVar "_hd" $ BType_Imm Bit64)
          BEnd_LittleEndian Bit32 ;
        (* deq(cid,tl)                           *)
        (* BDequeue is a macro, as yet undefined *)
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;


