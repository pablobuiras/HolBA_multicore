open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;

val _ = new_theory "faaAbstract";

(* r1, r2, r3 registers *)
(* r1: pointer to unsigned  *)
(* r2: value to add          *)
(* r3: the prior            *)
    
Definition faa_aprog_def:
  faa_aprog =
  BirProgram [
      <|bb_label := BL_Address_HC (Imm64 0w) "";
        bb_mc_tags := SOME <|mc_atomic := T; mc_acq := T; mc_rel := T|>;
        bb_statements :=
        [
          (* 0w: r3 = *r1 *)
          BStmt_Assign (BVar "r3" $ BType_Imm Bit64)
          $ Bexp_Load
              (BExp_Den $ BVar "MEM8" $ BType_Mem Bit64 Bit8)
              (BExp_Den $ BVar "r1" $ BType_Mem Bit64 Bit8)
              BEnd_LittleEndian Bit64  ;
          (* 4w: *r1 := r3 + r2 *)
          BStmt_Assign (BVar "ignore" $ BType_Imm Bit64)
            $ BExp_Store
              (BExp_Den $ BVar "MEM8" $ BType_Mem Bit64 Bit8)
              (BExp_Den $ BVar "r1" $ BType_Imm Bit64)
              BEnd_LittleEndian
              (BExp_BinExp
               BIExp_Add
               (BExp_Den $ BVar "r3" $ BType_Imm Bit64)
               (BExp_Den $ BVar "r2" $ BType_Imm Bit64))
        ] ;
        bb_last_statement :=
        BStmt_Jmp (BLE_Label $ BL_Address $ Imm64 4w) ;
      |> ;
  ]
End

val _ = export_theory();

