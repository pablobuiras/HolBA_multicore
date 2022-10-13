open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;

val _ = new_theory "casAbstract";

(* r1, r2, r3 registers *)
(* r1: pointer to unsigned, r1' = r1, *r1' = r2			 *)
(* r2: unsigned to compare, r3' = 1 if not(*r1 = r2)		 *)
(* r3: success flag, r3' = 1 if not(*r1 = r2), r3' = 0 otherwise *)
    
Definition cas_aprog_def:
  cas_aprog =
  BirProgram [
      <|bb_label := BL_Address_HC (Imm64 0w) "";
        bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
	HERTIL
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

