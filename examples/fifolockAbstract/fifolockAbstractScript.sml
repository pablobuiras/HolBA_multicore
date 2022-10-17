open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
val _ = new_theory "fifolockAbstract";

(*****************************************************************************)
(* Abstract fifo lock specification ******************************************)
(*****************************************************************************)
(* Pre:                                                                      *)
(* Post:                                                                     *)
(* Memory variables:                                                         *)
(*  - _hd: Queue head location                                               *)
(*  - _tl: Queue tail location                                               *)
(*  - _crit: Critical region flag                                            *)
(* Uses:                                                                     *)
(*  - queueAbstractScript                                                    *)

Definition fifo_lock_aprog_def:
  fifo_lock_aprog cid hd tl =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* enq(cid,_tl) *)
        enqueue_aprog (BExp_Den $ BVar "cid" $ BType_Imm Bit32)
          (BExp_Den $ BVar "_tl" $ BType_Imm Bit64)
          BEnd_LittleEndian Bit32 ;
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
  <|bb_label := BL_Address (Imm64 4w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
        (* _nxt = _hd(q) *)
        BStmt_Assign (BVar "_nxt" $ BType_Imm Bit32)
          $ BExp_Load (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
                      (BExp_Den $ BVar "_hd" $ BType_Imm Bit64)
                      BEnd_LittleEndian Bit32;
        (* _branch = nxt - cid *)
        BStmt_Assign (BVar "_branch" $ BType_Imm Bit8)
                     (BExp_BinExp BIExp_Minus
                       (BExp_Den $ BVar "_nxt" $ BType_Imm Bit32)
                       (BExp_Den $ BVar "cid" $ BType_Imm Bit32)) ;
      ];
    bb_last_statement :=
      BStmt_CJmp (BLE_Label (BL_Address (Imm64 12w)))
  |> ;
  <|bb_label := BL_Address (Imm64 12w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
        (* _crit = 1w *)                                                         
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_Const $ Imm64 1w ;
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))
  |> ;
] ;

Definition fifo_unlock_aprog_def:
  fifo_unlock_aprog cid hd tl =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* _crit = 0w *)
        BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
          $ BExp_Store (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
            (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
            BEnd_LittleEndian
            $ BExp_Const $ Imm64 0w ;
        (* deq(cid,_tl)                           *)
        dequeue_aprog (BExp_Den $ BVar "cid" $ BType_Imm Bit32)
          (BExp_Den $ BVar "_hd" $ BType_Imm Bit64)
          BEnd_LittleEndian Bit32 ;
      ];
    bb_last_statement :=
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;


