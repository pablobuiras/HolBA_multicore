open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
(* TODO currently some general definitions are in spinlockConcreteTheory *)
open spinlockConcreteTheory ;

val _ = new_theory "spinlockAbstract";

(* _GHOST.crit = 0w: lock is free *)
(* _GHOST.crit != 0w: lock is taken *)
(* We actually don't need the core id *)
    
Definition spinlock_aprog_def:
  spinlock_aprog cid =
  BirProgram [
      (* lock block *)
      <|bb_label := BL_Address_HC (Imm64 0w) "" ;
        bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
        bb_statements :=
        [
          (* if _GHOST.crit is non-zero, lock is busy *)
          (* 0w: jnz _GHOST.crit fail *)
          BStmt_CJmp
          (BExp_Den $ BVar "_GHOST" $ BType_Mem Bit64 Bit8)
          (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
          BEnd_LittleEndian ??
          (* not zero? *)
          (BLE_Label $ BL_Address $ Imm64 16w)
          (* zero? *)
          (BLE_Label $ BL_Address $ Imm64 4w);
          (* 4w: _GHOST.crit := 1 *)
          BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
            $ BExp_Store (BExp_Den $ (BVar "_GHOST" $ BType_Mem Bit64 Bit8)
              (BExp_Den $ BVar "crit" $ BType_Imm Bit64)
              BEnd_LittleEndian
              $ (BExp_Const $ Imm64 1w) ;
          (* 8w: success := 1w *)
          BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
            $ BExp_Store (BExp_Den $ BVar "success" $ BType_Imm Bit64)
              BEnd_LittleEndian
              $ (BExp_Const $ Imm64 1w) ;
          (* 12w: jmp 20w *)
          BStmt_Jmp
          (BLE_Label $ BL_Address $ Imm64 20w) ;
          (* 16w: success := 0w *)
          BStmt_Assign (BVar "_ignore" $ BType_Imm Bit64)
            $ BExp_Store (BExp_Den $ BVar "success" $ BType_Imm Bit64)
              BEnd_LittleEndian
              $ (BExp_Const $ Imm64 0w) ;
       ];
         bb_last_statement :=
           BStmt_Jmp
           (BLE_Label $ BBreakAtomic_Address $ Imm64 0w) ;
    |> ;
    <|bb_label := BL_Address (Imm64 24w) "" ;
    (* atomic or not, whatever is more convenient *)
      bb_mc_tags := SOME <| mc_atomic := T; mc_acq := F; mc_rel := F |> ;
      bb_statements :=
        [
          (* jz success BL_Address 0w *)
          BStmt_CJmp
           (BExp_Den $ BVar "success" $ BType_Imm Bit64)
           (BLE_Label $ BL_Address $ Imm64 28w)
           (BLE_Label $ BL_Address $ Imm64 0w);
        ] ;
      bb_last_statement :=
        BStmt_Jmp
        (BLE_Label $ BL_Address $ Imm64 32w) ;
        |> ;
           
           
          
               
            
                            
                         

                             
