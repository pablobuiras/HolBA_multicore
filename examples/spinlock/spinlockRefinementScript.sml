
open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
(* bir_promisingTheory ; *)
open bir_promisingGhostTheory;
open tracesTheory tracestepTheory spinlockTheory ;

val _ = new_theory "spinlockRefinement";

val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val (bir_spinlockfull_progbin_def, bir_spinlockfull_prog_def, bir_is_lifted_prog_spinlockfull) = lift_da_and_store_mc_riscv
          "spinlockfull"
          "spinlockfull.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

(*
returns the word with the cid's bit set to 1
0...010...0
     ^
    cid
*)
(* TODO functions between num and word, n2w? *)

Definition cid2w_def:
  cid2w (cid : num) = BExp_Const $ Imm64 (ARB : word64)
End

(*

- need assumption that GHOST.crit contains only zeros (= free)

check "ghost only" expression evaluations
- all memory assignment sub-expressions need to be ghost memories
- only assignment to ghost

*)

(* A spinlock definition that is parametrised by its core id.
 * The core id is used marking the lock taken. *)

Definition bir_spinlock_def:
  bir_spinlock cid =
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

val _ = export_theory();
