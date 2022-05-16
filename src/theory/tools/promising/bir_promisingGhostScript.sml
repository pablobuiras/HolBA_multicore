open HolKernel Parse boolLib bossLib;
open BasicProvers;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
open listRangeTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open stringTheory;

val _ = new_theory "bir_promisingGhost";

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val _ = Datatype‘
  mem_msg_t = <|
    loc : bir_val_t;
    val : bir_val_t;
    cid : num
    |>
’;

(* Type of instruction and their arguments. *)
Datatype:
  bir_statement_type_t =
  | BirStmt_Read bir_var_t bir_exp_t ((bir_cast_t # bir_immtype_t) option) bool bool bool
  | BirStmt_Write bir_exp_t bir_exp_t bool bool bool
  | BirStmt_Amo bir_var_t bir_exp_t bir_exp_t bool bool
  | BirStmt_Expr bir_var_t bir_exp_t
  | BirStmt_Fence bir_memop_t bir_memop_t
  | BirStmt_Branch bir_exp_t bir_label_exp_t bir_label_exp_t
  | BirStmt_Generic ('a bir_stmt_t)
  | BirStmt_None
End

(* Default value of memory *)
val mem_default_value_def = Define ‘
  mem_default_value = BVal_Imm (Imm64 0w)
’;

val mem_default_def = Define‘
  mem_default l = <| loc := l; val := mem_default_value; cid := ARB |>
’;

val mem_get_def = Define‘
   mem_get M l 0 = SOME (mem_default l)
   /\
   mem_get M l (SUC t) =
   case oEL t M of
   | SOME m => if m.loc = l then SOME m else NONE
   | NONE => NONE
’;

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
   mem_read M l t =
   case mem_get M l t of
   | SOME m => SOME m.val
   | NONE => NONE
’;

val mem_is_loc_def = Define‘
   mem_is_loc M 0 l = T
   /\
   mem_is_loc M (SUC t) l =
   case oEL t M of
   | SOME m => m.loc = l
   | NONE => F
’;

Theorem mem_get_is_loc:
  !M t l.
    IS_SOME (mem_get M l t) = mem_is_loc M t l
Proof
  Cases_on ‘t’ >|
  [
    fs [mem_get_def, mem_is_loc_def]
    ,
    fs [mem_get_def, mem_is_loc_def] >>
    rpt gen_tac >>
    rename1 ‘oEL t M’ >>
    Cases_on ‘oEL t M’ >|
    [
      fs []
      ,
      fs [] >>
      CASE_TAC >>
      (fs [])
    ]
  ]
QED

val mem_is_cid_def = Define‘
   mem_is_cid M 0 cid = F
   /\
   mem_is_cid M (SUC t) cid =
   case oEL t M of
   | SOME m => m.cid = cid
   | NONE => F
’;

(* Note that this currently does not take into account ARM *)
val mem_read_view_def = Define‘
  mem_read_view (f:fwdb_t) t = if f.fwdb_time = t ∧ ~f.fwdb_xcl then f.fwdb_view else t
’;

Definition bir_eval_view_of_exp:
  (bir_eval_view_of_exp (BExp_BinExp op e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_BinPred pred e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_UnaryExp op e) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Cast cty e ity) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Den v) viewenv =
    case FLOOKUP viewenv v of NONE => 0 | SOME view => view)
/\ (bir_eval_view_of_exp exp viewenv = 0)
End

(* ghost variables begin with an underscore *)

Definition is_ghost_def:
  is_ghost (BVar str ty) = isPREFIX "_" str
End

(* a ghost expression contains a ghost variable somewhere *)

Definition is_ghost_exp_def:
  is_ghost_exp (BExp_BinExp op e1 e2) = (is_ghost_exp e1 \/ is_ghost_exp e2)
  /\ is_ghost_exp (BExp_BinPred pred e1 e2) = (is_ghost_exp e1 \/ is_ghost_exp e2)
  /\ is_ghost_exp (BExp_UnaryExp op e) = is_ghost_exp e
  /\ is_ghost_exp (BExp_Cast cty e ity) = is_ghost_exp e
  /\ is_ghost_exp (BExp_Den v) = is_ghost v
  /\ is_ghost_exp (BExp_IfThenElse c et ef) = (is_ghost_exp et \/ is_ghost_exp ef)
  /\ is_ghost_exp (BExp_Load mem_e a_e en ty) = is_ghost_exp a_e
  /\ is_ghost_exp (BExp_Store mem_e a_e en v_e) = (is_ghost_exp a_e \/ is_ghost_exp v_e)
  /\ is_ghost_exp _ = F
End

(* a ghost statement contains a ghost expression *)

Definition is_ghost_stmt_def:
  is_ghost_stmt (BStmtB $ BStmt_Assign var e) = (is_ghost var \/ is_ghost_exp e)
  /\ is_ghost_stmt (BStmtE $ BStmt_CJmp e _ _) = is_ghost_exp e
  /\ is_ghost_stmt _ = F
End

(* read from ghost memory if variable is prefixed with an underscore, else use
 * the usual environment *)

Definition bir_eval_exp_ghost_def:
  (bir_eval_exp_ghost (BExp_Const n) env g_env = SOME (BVal_Imm n)) /\
  (bir_eval_exp_ghost (BExp_MemConst aty vty mmap) env g_env = SOME (BVal_Mem aty vty mmap)) /\
  (bir_eval_exp_ghost (BExp_Den v) env g_env =
    if is_ghost v
    then bir_env_read v g_env
    else bir_env_read v env) /\
  (bir_eval_exp_ghost (BExp_Cast ct e ty) env g_env = bir_eval_cast ct (bir_eval_exp_ghost e env g_env) ty) /\
  (bir_eval_exp_ghost (BExp_UnaryExp et e) env g_env = bir_eval_unary_exp et (bir_eval_exp_ghost e env g_env)) /\
  (bir_eval_exp_ghost (BExp_BinExp et e1 e2) env g_env = bir_eval_bin_exp et (bir_eval_exp_ghost e1 env g_env) (bir_eval_exp_ghost e2 env g_env)) /\
  (bir_eval_exp_ghost (BExp_BinPred pt e1 e2) env g_env = bir_eval_bin_pred pt (bir_eval_exp_ghost e1 env g_env) (bir_eval_exp_ghost e2 env g_env)) /\
  (bir_eval_exp_ghost (BExp_MemEq e1 e2) env g_env = bir_eval_memeq (bir_eval_exp_ghost e1 env g_env) (bir_eval_exp_ghost e2 env g_env)) /\
  (bir_eval_exp_ghost (BExp_IfThenElse c et ef) env g_env =
    bir_eval_ifthenelse (bir_eval_exp_ghost c env g_env) (bir_eval_exp_ghost et env g_env) (bir_eval_exp_ghost ef env g_env)) /\
  (bir_eval_exp_ghost (BExp_Load mem_e a_e en ty) env g_env =
    bir_eval_load (bir_eval_exp_ghost mem_e env g_env) (bir_eval_exp_ghost a_e env g_env) en ty) /\
  (bir_eval_exp_ghost (BExp_Store mem_e a_e en v_e) env g_env =
    bir_eval_store (bir_eval_exp_ghost mem_e env g_env) (bir_eval_exp_ghost a_e env g_env) en (bir_eval_exp_ghost v_e env g_env))
End

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
Definition bir_eval_exp_view_def:
  bir_eval_exp_view exp env viewenv g_env =
  (bir_eval_exp_ghost exp env g_env, bir_eval_view_of_exp exp viewenv)
End

val exp_is_load_def = Define `
  (exp_is_load (BExp_Load _ _ _ _) = T) /\
  (exp_is_load _ = F)
`;

val stmt_generic_step_def = Define`
   stmt_generic_step (BStmtB (BStmt_Assign _ _)) = F
/\ stmt_generic_step (BStmtB (BStmt_Fence _ _)) = F
/\ stmt_generic_step (BStmtE (BStmt_CJmp _ _ _)) = F
/\ stmt_generic_step _ = T
`;

val is_read_def = Define`
   is_read BM_Read = T
/\ is_read BM_Write = F
/\ is_read BM_ReadWrite = T
`;

val is_write_def = Define`
   is_write BM_Read = F
/\ is_write BM_Write = T
/\ is_write BM_ReadWrite = T
`;

(*
(* Checks if the memory expressions from lifted loads and stores
 * refers to regular memory or dummy memory. May look inside casts *)
(* TODO: Clarify *)
val contains_dummy_mem_def = Define`
  (contains_dummy_mem (BExp_Den (BVar mem_name mem_ty)) =
     if mem_name <> "MEM8" (* RISC-V regular memory *)
     then T
     else F) /\
  (contains_dummy_mem (BExp_Load mem_e a_e en ty) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Store mem_e a_e en v_e) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Cast cast_ty e imm_ty) =
     contains_dummy_mem e) /\
  (contains_dummy_mem _ = F)
`;
*)

(* Obtains an option type that contains the load arguments
 * needed to apply the read rule (can look inside one cast) *)
Definition get_read_args_def:
  (get_read_args (BExp_Load mem_e a_e en ty) = SOME (a_e, NONE)) /\
  (get_read_args (BExp_Cast cast_ty load_e imm_ty) =
   case get_read_args load_e of
   | SOME (a_e, NONE) => SOME (a_e, SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_read_args _ = NONE)
End

(* Obtains an GhostOption type that contains the store arguments
 * needed to apply the fulfil rule *)
(* is ghost ==> any store is to a ghost var/mem *)
Definition get_fulfil_args_def:
  (get_fulfil_args (BExp_IfThenElse cond_e e1 e2) = get_fulfil_args e1) /\
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) = SOME (a_e, v_e)) /\
  (get_fulfil_args _ = NONE)
End

Theorem get_read_fulfil_args_exclusive:
∀e.
  (IS_SOME $ get_read_args e ⇒ get_fulfil_args e = NONE)
∧ (IS_SOME $ get_fulfil_args e ⇒ get_read_args e = NONE)
Proof
  Cases >>
  fs [get_read_args_def, get_fulfil_args_def]
QED

val get_xclb_view_def = Define`
  get_xclb_view (SOME xclb) = xclb.xclb_view
∧ get_xclb_view NONE = 0
`;

val fulfil_atomic_ok_def = Define`
  fulfil_atomic_ok M l cid t_r t_w =
     (mem_is_loc M t_r l ==>
       !t'. (t_r < t' /\ t' < t_w /\ mem_is_loc M t' l) ==> mem_is_cid M t' cid)
`;

val env_update_cast64_def = Define‘
  env_update_cast64 varname (BVal_Imm v) vartype env =
    bir_env_update varname (BVal_Imm (n2bs (b2n v) Bit64)) vartype env
’;

val fulfil_update_env_def = Define`
  fulfil_update_env p s xcl =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) =>
        bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 0w)) (bir_var_type var_succ) s.bst_environ
      | _ => NONE
    else SOME s.bst_environ
`;

val fulfil_update_viewenv_def = Define`
  fulfil_update_viewenv p s xcl v_post =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) => SOME (s.bst_viewenv |+ (var_succ, v_post))
      | _ => NONE
    else SOME s.bst_viewenv
`;

val xclfail_update_env_def = Define`
  xclfail_update_env p s =
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) =>
        bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 1w)) (bir_var_type var_succ) s.bst_environ
      | _ => NONE
`;

val xclfail_update_viewenv_def = Define`
  xclfail_update_viewenv p s =
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) => SOME (s.bst_viewenv |+ (var_succ, 0))
      | _ => NONE
`;

(* Upon the loading statement that is the first Assign in a lifted
 * Load-type instruction, checks if the block is trying to model
 * an exclusive-load *)
Definition is_xcl_read_def:
  is_xcl_read p pc a_e =
    case bir_get_current_statement p (bir_pc_next pc) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
                       var BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))))) => var = a_e
     | _ => F
End

(* Upon the storing statement that is the first Assign in a lifted
 * Strore-type instruction, checks if the block is trying to model
 * an exclusive-store *)
val is_xcl_write_def = Define‘
  is_xcl_write p pc =
    case bir_get_current_statement p (bir_pc_next (bir_pc_next pc)) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))))) => T
     | _ => F
’;

(* properties about exclusive reads and writes *)

Theorem is_xcl_read_thm:
  !p pc a_e. is_xcl_read p pc a_e <=>
    bir_get_current_statement p (bir_pc_next pc) =
      SOME $ BStmtB $ BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
        $ BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
          a_e BEnd_LittleEndian
          (BExp_Const (Imm32 0x1010101w))
Proof
  rw[is_xcl_read_def,EQ_IMP_THM,optionTheory.IS_SOME_EXISTS]
  >> pop_assum mp_tac
  >> rpt (BasicProvers.PURE_TOP_CASE_TAC >> fs[])
QED

Theorem is_xcl_write_thm:
  !p pc. is_xcl_write p pc <=>
    IS_SOME $ bir_get_current_statement p (bir_pc_next $ bir_pc_next pc) /\
    bir_get_current_statement p (bir_pc_next $ bir_pc_next pc) =
      SOME $ BStmtB $ BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
        $ BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))
Proof
  rw[is_xcl_write_def,EQ_IMP_THM,optionTheory.IS_SOME_EXISTS]
  >- (BasicProvers.full_case_tac >> fs[])
  >> pop_assum mp_tac
  >> rpt (BasicProvers.PURE_TOP_CASE_TAC >> fs[])
QED

val is_acq_def = Define‘
  is_acq p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_acq
         | _ => F)
     | _ => F
’;

val is_rel_def = Define‘
  is_rel p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_rel
         | _ => F)
     | _ => F
’;

val is_amo_def = Define‘
  is_amo p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_atomic
         | _ => F)
     | _ => F
’;

Definition bir_get_stmt_def:
  bir_get_stmt p pc =
  case bir_get_current_statement p pc of
  | SOME (BStmtB (BStmt_Assign var e)) =>
      if is_amo p pc then
      (case get_read_args e of
       | SOME (a_e, cast_opt) =>
           (case bir_get_current_statement p (bir_pc_next pc) of
           | SOME (BStmtB (BStmt_Assign var' e)) =>
               (case get_fulfil_args e of
               | SOME (a_e', v_e) =>
                   if a_e = a_e'
                   then BirStmt_Amo var a_e v_e (is_acq p pc) (is_rel p pc)
                   else BirStmt_None
               | NONE => BirStmt_None)
           | _ => BirStmt_None)
       | NONE =>
           (case get_fulfil_args e of
            | SOME (a_e, v_e) => BirStmt_None
            | NONE => BirStmt_Expr var e))
      else
       (case get_read_args e of
       | SOME (a_e, cast_opt) => BirStmt_Read var a_e cast_opt (is_xcl_read p pc a_e) (is_acq p pc) (is_rel p pc)
       | NONE =>
           (case get_fulfil_args e of
           | SOME (a_e, v_e) => BirStmt_Write a_e v_e (is_xcl_write p pc) (is_acq p pc) (is_rel p pc)
           | NONE => BirStmt_Expr var e))
  | SOME (BStmtB (BStmt_Fence K1 K2)) => BirStmt_Fence K1 K2
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) => BirStmt_Branch cond_e lbl1 lbl2
  | SOME stmt => BirStmt_Generic stmt
  | NONE => BirStmt_None
End

Theorem bir_get_stmt_read:
∀p pc stmt var a_e cast_opt xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Read var a_e cast_opt xcl acq rel) ⇔
 (∃e.
 bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ ~is_amo p pc
 /\ get_read_args e = SOME (a_e, cast_opt)
 /\ is_xcl_read p pc a_e = xcl
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  gvs [bir_get_stmt_def, AllCaseEqs(),
       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem bir_get_stmt_write:
∀p pc stmt a_e v_e xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Write a_e v_e xcl acq rel) ⇔
 (∃var e. bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ ~is_amo p pc
 /\ get_fulfil_args e = SOME (a_e, v_e)
 /\ is_xcl_write p pc = xcl
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  rw [bir_get_stmt_def,AllCaseEqs()] >>
  eq_tac >>
  rw [get_read_fulfil_args_exclusive]
QED

Theorem bir_get_stmt_amo:
∀p pc var stmt a_e v_e xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Amo var a_e v_e acq rel) ⇔
 (∃e cast_opt var' e'.
    bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ is_amo p pc
 /\ get_read_args e = SOME (a_e, cast_opt)
 /\ bir_get_current_statement p (bir_pc_next pc) = SOME (BStmtB (BStmt_Assign var' e'))
 /\ get_fulfil_args e' = SOME (a_e, v_e)
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  gvs [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem bir_get_stmt_expr:
∀p pc var e.
 (bir_get_stmt p pc = BirStmt_Expr var e) =
 (bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ get_read_args e = NONE
 /\ get_fulfil_args e = NONE)
Proof
  rw [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
  Cases_on ‘is_amo p pc’ >> rw []
QED

Theorem bir_get_stmt_fence:
∀p pc K1 K2.
 (bir_get_stmt p pc = BirStmt_Fence K1 K2) ⇔
 bir_get_current_statement p pc = SOME (BStmtB (BStmt_Fence K1 K2))
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_branch:
∀p pc cond_e lbl1 lbl2.
 (bir_get_stmt p pc = BirStmt_Branch cond_e lbl1 lbl2) ⇔
 bir_get_current_statement p pc = SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2))
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_generic:
∀p pc stmt.
 (bir_get_stmt p pc = BirStmt_Generic stmt ⇔
 (bir_get_current_statement p pc = SOME stmt ∧ stmt_generic_step stmt))
Proof
  rpt strip_tac >>
  Cases_on ‘stmt’ >|
  [rename1 ‘BStmtB b’, rename1 ‘BStmtE b’] >>
  (
    Cases_on ‘b’ >>
    gvs [bir_get_stmt_def,stmt_generic_step_def,AllCaseEqs()]
  )
QED

(* FIX THIS???
Theorem bir_get_stmt_none:
∀p pc.
 (bir_get_stmt p pc = BirStmt_None) ⇔
 bir_get_current_statement p pc = NONE \/
Proof
  fs [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED
*)

(* TODO: "Generalising variable "v_pre" in clause #0"? *)
(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v a_e xcl acq rel M l (t:num) v_pre v_post v_addr var new_env cid opt_cast.
   bir_get_stmt p s.bst_pc = BirStmt_Read var a_e opt_cast xcl acq rel
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv g_env
 /\ ~is_ghost_exp a_e
 ∧ mem_read M l t = SOME v
 ∧ v_pre = MAX (MAX (MAX v_addr s.bst_v_rNew) (if (acq /\ rel) then s.bst_v_Rel else 0))
               (if (acq /\ rel) then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX v_pre (s.bst_coh l))) ⇒ ~(mem_is_loc M t' l))
 ∧ v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 (* TODO: Update viewenv by v_addr or v_post? *)
 ∧ s' = s with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
                  bst_environ := new_env;
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_rNew := if acq then (MAX s.bst_v_rNew v_post) else s.bst_v_rNew;
                  bst_v_wNew := if acq then (MAX s.bst_v_wNew v_post) else s.bst_v_wNew;
                  bst_v_Rel := MAX s.bst_v_Rel (if (rel /\ acq) then v_post else 0);
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_xclb := if xcl
                              then SOME <| xclb_time := t; xclb_view := v_post |>
                              else s.bst_xclb;
                  bst_pc := if xcl
                            then (bir_pc_next o bir_pc_next) s.bst_pc
                            else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M g_env [] s' g_env')
/\ (* exclusive-failure *)
(!p s s' M a_e v_e acq rel cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e T acq rel
 /\ ~is_ghost_exp a_e
 /\  SOME new_env = xclfail_update_env p s
 /\  SOME new_viewenv = xclfail_update_viewenv p s
 /\  s' = s with <| bst_environ := new_env;
                    bst_viewenv := new_viewenv;
                    bst_xclb := NONE;
                    bst_pc := (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc |>
 ==>
clstep p cid s M g_env [] s' g_env)
/\ (* fulfil *)
(!p s s' M v a_e xcl acq rel l (t:num) v_pre v_post v_addr v_data v_e cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel
 /\ ~is_ghost_exp a_e
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv g_env
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv g_env
 /\ (xcl ==> s.bst_xclb <> NONE /\ fulfil_atomic_ok M l cid (THE s.bst_xclb).xclb_time t)
 /\ MEM t s.bst_prom
 /\ mem_get M l t = SOME <| loc := l; val := v; cid := cid  |>
 (* TODO: Use get_xclb_view or separate conjunct to extract option type? *)
 /\ v_pre = MAX (MAX (MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
                          (if rel
                           then (MAX s.bst_v_rOld s.bst_v_wOld)
                           else 0))
                     (if (xcl /\ acq /\ rel)
                      then s.bst_v_Rel
                      else 0))
                (if xcl
                 then get_xclb_view s.bst_xclb
                 else 0)
 /\ (MAX v_pre (s.bst_coh l) < t)
 /\ v_post = t
 /\ SOME new_env = fulfil_update_env p s xcl
 (* TODO: Update viewenv by v_post or something else? *)
 /\ SOME new_viewenv = fulfil_update_viewenv p s xcl v_post
 /\ s' = s with <| bst_viewenv := new_viewenv;
                   bst_prom updated_by (FILTER (\t'. t' <> t));
                   bst_environ := new_env;
                   bst_coh := (\lo. if lo = l
                                    then MAX (s.bst_coh l) v_post
                                    else s.bst_coh(lo));
                   bst_v_wOld := MAX s.bst_v_wOld v_post;
                   bst_v_CAP := MAX s.bst_v_CAP v_addr;
                   bst_v_Rel := MAX s.bst_v_Rel (if (rel /\ acq) then v_post else 0);
                   bst_v_rNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_rNew v_post) else s.bst_v_rNew;
                   bst_v_wNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_wNew v_post) else s.bst_v_wNew;
                   bst_fwdb := (\lo. if lo = l
                                     then <| fwdb_time := t;
                                             fwdb_view := MAX v_addr v_data;
                                             fwdb_xcl := xcl |>
                                     else s.bst_fwdb(lo));
                   bst_xclb := if xcl
                               then NONE
                               else s.bst_xclb;
                   bst_pc := if xcl
                             then (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc
                             else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M g_env [t] s' g_env')
/\ (* AMO fulfil *)
(!p cid s s' M acq rel var l a_e v_r v_w v_e v_rPre v_rPost v_wPre v_wPost (t_w:num) (t_r :num) new_environ new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel
   /\ ~is_ghost_exp a_e
   /\ ~is_ghost_exp v_e
   /\ ~is_ghost var
   (* Get location *)
   /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv g_env

   (* Read part *)
   /\ mem_read M l t_r = SOME v_r (* v_r value read *)
   /\ v_rPre = MAX v_addr (
        MAX s.bst_v_rNew
        (if acq /\ rel then (MAX s.bst_v_Rel (MAX s.bst_v_rOld s.bst_v_wOld)) else 0))
   /\ v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r)

   (* register and register view update *)
   /\ SOME new_environ = env_update_cast64 (bir_var_name var) v_r (bir_var_type var) (s.bst_environ)
   /\ new_viewenv = FUPDATE s.bst_viewenv (var, v_rPost)

   (* Write part *)
   /\ MEM t_w s.bst_prom
   (* v_w value to write, v_e value expression *)
   /\ (SOME v_w, v_data) = bir_eval_exp_view v_e new_environ new_viewenv g_env
   /\ mem_get M l t_w = SOME <| loc := l; val := v_w; cid := cid |>
   /\ v_wPre = MAX v_addr (
        MAX v_data (
        MAX s.bst_v_CAP (
        MAX v_rPost (
        MAX s.bst_v_wNew (
        MAX (if rel then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
             (if (acq /\ rel) then s.bst_v_Rel else 0))))))
   /\ v_wPost = t_w
   /\ MAX v_wPre (s.bst_coh l) < t_w

   (* No writes to memory location between read and write *)
   /\ (!t'. t_r < t' /\ t' < t_w ==> mem_is_loc M t' l)

   (* State update *)
   /\ s' = s with <| bst_viewenv := new_viewenv;
                     bst_environ := new_environ;
                     bst_prom    updated_by (FILTER (\t'. t' <> t_w));
                     bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_wPost);
                     bst_v_Rel   updated_by (MAX (if acq /\ rel then v_wPost else 0));
                     bst_v_rOld  updated_by (MAX v_rPost);
                     bst_v_rNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_wNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_CAP   updated_by (MAX v_addr);
                     bst_v_wOld  updated_by (MAX v_wPost);
                     bst_fwdb    updated_by (l =+ <| fwdb_time := t_w;
                                                     fwdb_view := MAX v_addr v_data;
                                                     fwdb_xcl := T |>);
                     bst_pc updated_by (bir_pc_next o bir_pc_next) |>
 ==>
  clstep p cid s M g_env [t_w] s' g_env')
/\ (* fence *)
(!p s s' K1 K2 M cid v.
   bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2
   /\ v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                     bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
                     bst_pc updated_by bir_pc_next |>
==>
  clstep p cid s M g_env [] s' g_env)
/\ (* branch (conditional jump) *)
(!p s s' M cid v oo s2 v_addr cond_e lbl1 lbl2 stm.
   bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2
    /\ ~is_ghost_exp cond_e
    /\ stm = BStmtE (BStmt_CJmp cond_e lbl1 lbl2)
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv g_env
    /\ bir_exec_stmt p stm s = (oo,s2)
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>
==>
  clstep p cid s M g_env [] s' g_env)
/\ (* register-to-register operation *)
(!p s s' var M cid v v_val e new_env.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e
 /\ ~is_ghost var /\ ~is_ghost_exp e
 /\ (SOME v, v_val) = bir_eval_exp_view e s.bst_environ s.bst_viewenv g_env
 /\ NONE = get_read_args e
 /\ NONE = get_fulfil_args e
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 /\ s' = s with <| bst_environ := new_env;
                   bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                   bst_pc      updated_by bir_pc_next |>
==> clstep p cid s M g_env [] s' g_env')
/\ (* Other BIR single steps *)
(!p s s' M cid stm oo.
   bir_get_stmt p s.bst_pc = BirStmt_Generic stm
    /\ ~is_ghost_stmt stm
    /\ bir_exec_stmt p stm s = (oo,s')
==>
  clstep p cid s M g_env [] s' g_env)
/\ (* assign to ghost location *)
(!p s g_env g_env' var M cid v e.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e
 /\ is_ghost_exp e /\ is_ghost var
 /\ (SOME v, _) = bir_eval_exp_view e s.bst_environ s.bst_viewenv g_env
 /\ SOME g_env' = env_update_cast64 (bir_var_name var) v (bir_var_type var) g_env
==> clstep p cid s M g_env [] s g_env')
`;


(* core steps *)
val (bir_cstep_rules, bir_cstep_ind, bir_cstep_cases) = Hol_reln`
(* execute *)
(!p cid s M s' prom.
  clstep p cid s M g_env prom s' g_env'
==>
  cstep p cid s M g_env prom s' M' g_env')

/\ (* promise *)
(!p cid s M s' t msg.
   (msg.cid = cid
   /\ t = LENGTH M + 1
   /\ s' = s with bst_prom updated_by (\pr. pr ++ [t]))
==>
  cstep p cid s M g_env [t] s' (M ++ [msg]) g_env)
`;

(* core steps seq *)
val (bir_cstep_seq_rules, bir_cstep_seq_ind, bir_cstep_seq_cases) = Hol_reln`
(* seq *)
(!p cid s M g_env s' prom g_env'.
  clstep p cid s M g_env (prom:num list) s' g_env'
==>
  cstep_seq p cid (s, M) (s', M))

/\ (* write *)
(!p cid s M g_env s' s'' M' g_env' t.
  (cstep p cid s M g_env [t] s' M' g_env' /\ ~(M = M')
  /\ clstep p cid s' M' g_env [t] s'' g_env')
==>
  cstep_seq p cid (s, M) (s'', M'))
`;

val cstep_seq_rtc_def = Define`cstep_seq_rtc p cid = (cstep_seq p cid)^*`

(*
(*
 * properties about cstep, clstep, cstep_seq
 *)

(* the timestamp of a fulfil is coupled to the fulfiled core *)

Theorem cstep_fulfil_to_memory:
  !t p cid s M s' g_env g_env'.
  cstep p cid s M g_env [t] s' M g_env'
  ==> 0 < t /\ PRE t < LENGTH M /\ (EL (PRE t) M).cid = cid
Proof
  Cases >> rpt gen_tac >> strip_tac
  >> gvs[bir_cstep_cases,bir_clstep_cases,PULL_EXISTS,arithmeticTheory.PRE_SUB1,oEL_THM,oEL_THM,mem_get_def,AllCaseEqs()]
QED

(* memory only ever increases *)

Theorem cstep_seq_IS_PREFIX:
  !p cid sM sM'. cstep_seq p cid sM sM'
  ==> IS_PREFIX (SND sM') (SND sM)
Proof
  ho_match_mp_tac bir_cstep_seq_ind >> rw[]
  >> fs[bir_cstep_cases]
QED

Theorem cstep_seq_rtc_IS_PREFIX:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  ==> IS_PREFIX (SND sM') (SND sM)
Proof
  ntac 2 gen_tac
  >> fs[cstep_seq_rtc_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> rw[]
  >> dxrule_then assume_tac cstep_seq_IS_PREFIX
  >> imp_res_tac rich_listTheory.IS_PREFIX_TRANS
QED

(* a fulfil is only fulfilled once *)

Theorem clstep_fulfil_once:
  !p cid cid' s M t s' s''.
  clstep p cid s M [t] s'
  /\ clstep p cid' s' M [t] s'' ==> F
Proof
  rpt strip_tac
  >> Cases_on `cid = cid'`
  >> gvs[bir_clstep_cases,MEM_FILTER]
QED

Theorem cstep_seq_rtc_fulfil_once:
  !p cid sM2 sM3 s M t s1 cid' t' s4 M4 s5.
  cstep p cid s M [t] s1 (SND sM2)
  /\ clstep p cid s1 (SND sM2) [t] (FST sM2)
  /\ cstep_seq_rtc p cid sM2 sM3
  /\ cstep p cid' (FST sM3) (SND sM3) [t'] s4 M4
  /\ clstep p cid' s4 M4 [t'] s5
  ==> t <> t'
Proof
  rpt strip_tac
  >> imp_res_tac cstep_seq_rtc_IS_PREFIX
  >> gvs[bir_cstep_cases]
  >> imp_res_tac clstep_fulfil_once
  >> rpt $ PRED_ASSUM is_forall kall_tac
  >> gvs[rich_listTheory.IS_PREFIX_APPEND]
QED
*)

(* bir_exec_stmt invariants *)

Theorem bir_exec_stmt_BStmtE_BStmt_CJmp_bst_xclb_EQ:
  !p cond_e lbl1 lbl2 s oo s'.
  bir_exec_stmt p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s = (oo,s')
  ==> s.bst_xclb = s'.bst_xclb
Proof
  EVAL_TAC
  >> rw[AllCaseEqs()]
  >> fs[]
QED

Theorem bir_exec_stmt_stmt_generic_step_bst_xclb_EQ:
  !stm p s oo s'. bir_exec_stmt p stm s = (oo,s')
  /\ stmt_generic_step stm
  ==> s.bst_xclb = s'.bst_xclb
Proof
  Cases >> rpt strip_tac
  >> (qmatch_asmsub_rename_tac `BStmtE stm`
    ORELSE qmatch_asmsub_rename_tac `BStmtB stm`)
  >> Cases_on `stm`
  >> gs[bir_get_stmt_generic,stmt_generic_step_def,bir_exec_stmt_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def,bir_exec_stmt_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_exec_stmtB_def,bir_state_is_terminated_def,bir_exec_stmt_assign_def,
    bir_exec_stmtB_def,bir_exec_stmt_assert_def,AllCaseEqs(),
    bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_exec_stmt_assume_def,
    bir_exec_stmt_observe_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,
    bir_exec_stmt_jmp_to_label_def,bir_exec_stmtE_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac >> fs[]
QED

Theorem stmt_generic_step_bst_prom_EQ:
  !stm p s oo s'. stmt_generic_step stm
  /\ bir_exec_stmt p stm s = (oo,s')
  ==> s.bst_prom = s'.bst_prom
Proof
  Cases >> rpt strip_tac
  >- (
    qmatch_asmsub_rename_tac `BStmtB b`
    >> Cases_on `b`
    >> gvs[stmt_generic_step_def,bir_programTheory.bir_exec_stmt_def,pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_programTheory.bir_exec_stmtB_def,bir_programTheory.bir_exec_stmt_assert_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_assume_def,bir_programTheory.bir_exec_stmt_observe_def]
    >> BasicProvers.every_case_tac
    >> fs[]
  )
  >> qmatch_asmsub_rename_tac `BStmtE b`
  >> Cases_on `b`
  >> gvs[AllCaseEqs(),bir_exec_stmtB_def,bir_exec_stmtE_def,
    bir_exec_stmt_assert_def,bir_exec_stmt_assign_def,bir_exec_stmt_assume_def,
    bir_exec_stmt_cjmp_def,bir_exec_stmt_def,bir_exec_stmt_fence_def,
    bir_exec_stmt_halt_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,
    bir_exec_stmt_observe_def,bir_state_is_terminated_def,
    bir_state_set_typeerror_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem bir_exec_stmt_BStmtE_BStmt_CJmp_bst_prom_EQ:
  !p cond_e lbl1 lbl2 s oo s'.
  bir_exec_stmt p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s = (oo,s')
  ==> s.bst_prom = s'.bst_prom
Proof
  EVAL_TAC
  >> rw[AllCaseEqs()]
  >> fs[]
QED

(* set of promises contains only elements smaller then the memory *)

Theorem clstep_EVERY_LENGTH_bst_prom_inv:
  !p cid s M g_env prom s' g_env'. clstep p cid s M g_env prom s' g_env'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH M) s.bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH M) s'.bst_prom
Proof
  rw[bir_clstep_cases,bir_get_stmt_generic]
  >> imp_res_tac bir_exec_stmt_BStmtE_BStmt_CJmp_bst_prom_EQ
  >> imp_res_tac stmt_generic_step_bst_prom_EQ
  >> fs[]
  >> qhdtm_x_assum `EVERY` mp_tac
  >> fs[EVERY_FILTER]
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem clstep_bst_prom_NOT_EQ:
  !p cid s M g_env t s' g_env'.
  clstep p cid s M g_env [t] s' g_env' ==> s.bst_prom <> s'.bst_prom
Proof
  rw[bir_clstep_cases,bir_get_stmt_write]
  >> fs[Once EQ_SYM_EQ,FILTER_NEQ_ID]
QED

Theorem clstep_LENGTH_prom:
  !p cid s M g_env prom s' g_env'. clstep p cid s M g_env prom s' g_env'
  ==> prom = [] \/ ?t. prom = [t]
Proof
  rw[bir_clstep_cases]
QED


(* cstep_seq invariant *)

Theorem bir_exec_stmt_jmp_bst_prom:
  !st p lbl. st.bst_prom = (bir_exec_stmt_jmp p lbl st).bst_prom
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

Theorem clstep_bst_prom_EQ:
!p cid st M g_env st' g_env'.
  clstep p cid st M g_env [] st' g_env' ==> st.bst_prom = st'.bst_prom
Proof
  rw[bir_clstep_cases]
  >> gvs[bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_bst_prom,bir_get_stmt_def]
  >> (
    fs[AllCaseEqs(),bir_exec_stmt_def,pairTheory.ELIM_UNCURRY,bir_exec_stmt_halt_def]
    >> BasicProvers.every_case_tac
    >> fs[bir_exec_stmtB_def,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_observe_def]
    >> BasicProvers.every_case_tac
    >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
  )
  >> qmatch_assum_rename_tac `stmt_generic_step $ BStmtE b`
  >> Cases_on `b`
  >> fs[stmt_generic_step_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_exec_stmt_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
QED

(*
Theorem cstep_seq_bst_prom_EQ:
  !p cid sM sM'. cstep_seq p cid sM sM'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM') (FST sM').bst_prom
    /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac bir_cstep_seq_ind
  >> conj_tac >> rpt gen_tac >> strip_tac
  >- cheat
  >> strip_tac >> conj_asm1_tac
  >- (
    pop_assum mp_tac
    >> gvs[bir_cstep_cases,bir_clstep_cases,rich_listTheory.FILTER_APPEND,EVERY_FILTER, rich_listTheory.FILTER_IDEM]
    >> match_mp_tac EVERY_MONOTONIC
    >> fs[]
  )
  >> gvs[bir_clstep_cases,bir_cstep_cases,bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,bir_state_set_typeerror_def,stmt_generic_step_def,bir_exec_stmt_jmp_bst_prom,rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_IDEM, MEM_FILTER]
  >> fs[Once EQ_SYM_EQ,FILTER_EQ_ID]
  >> qpat_x_assum `EVERY _ _.bst_prom` mp_tac
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem cstep_seq_rtc_bst_prom_EQ:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM') (FST sM').bst_prom
    /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO,cstep_seq_rtc_def]
  >> ntac 2 gen_tac
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> drule_all cstep_seq_bst_prom_EQ
  >> fs[]
QED
*)

val is_certified_def = Define`
is_certified p cid s M = ?s' M'.
  cstep_seq_rtc p cid (s, M) (s', M')
  /\ s'.bst_prom = []
`;

val _ = Datatype `core_t =
  Core num (string bir_program_t) bir_state_t
`;

val get_core_cid = Define‘
   get_core_cid (Core cid p s) = cid
’;

val get_core_prog = Define‘
   get_core_prog (Core cid p s) = p
’;

val get_core_state = Define‘
   get_core_state (Core cid p s) = s
’;



val cores_pc_not_atomic_def = Define`
  cores_pc_not_atomic cores =
    ~?cid p s i bl mc_tags.
     FLOOKUP cores cid = SOME (Core cid p s)
     /\ s.bst_pc.bpc_index <> 0
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, bl)
     /\ bl.bb_mc_tags = SOME mc_tags
     /\ mc_tags.mc_atomic = T
`;

val atomicity_ok_def = Define`
  atomicity_ok cid cores =
    cores_pc_not_atomic (cores \\ cid)
`;

(* system step *)
val (bir_parstep_rules, bir_parstep_ind, bir_parstep_cases) = Hol_reln`
(!p cid s s' M M' cores prom.
   (FLOOKUP cores cid = SOME (Core cid p s)
    /\ atomicity_ok cid cores
    /\ cstep p cid s M g_env prom s' M' g_env'
    /\ is_certified p cid s' M')
==>
   parstep cid cores M g_env (FUPDATE cores (cid, Core cid p s')) M' g_env')
`;


Theorem bir_exec_stmt_mc_invar:
!stmt prog state oo state'.
bir_exec_stmt prog stmt state = (oo,state') ==>
(state.bst_viewenv = state'.bst_viewenv) /\
(state.bst_coh = state'.bst_coh) /\
(state.bst_v_rOld = state'.bst_v_rOld) /\
(state.bst_v_wOld = state'.bst_v_wOld) /\
(state.bst_v_rNew = state'.bst_v_rNew) /\
(state.bst_v_wNew = state'.bst_v_wNew) /\
(state.bst_v_CAP = state'.bst_v_CAP) /\
(state.bst_v_Rel = state'.bst_v_Rel) /\
(state.bst_prom = state'.bst_prom) /\
(state.bst_fwdb = state'.bst_fwdb) /\
(state.bst_xclb = state'.bst_xclb) /\
(state.bst_inflight = state'.bst_inflight) /\
(state.bst_counter = state'.bst_counter)
Proof
Induct_on ‘stmt’ >> Induct_on ‘b’ >> (
 REPEAT GEN_TAC >>
 STRIP_TAC
) >| [
 fs [bir_exec_stmt_def, bir_exec_stmtB_def] >>
 Cases_on ‘bir_state_is_terminated (bir_exec_stmt_assign b b0 state)’ >> (
  fs [bir_exec_stmt_assign_def] >>
  Cases_on ‘bir_eval_exp b0 state.bst_environ’ >> (
   fs [bir_state_set_typeerror_def, bir_state_t_component_equality]
  ) >>
  Cases_on ‘bir_env_write b x state.bst_environ’ >- (
   fs []
  ) >>
  Cases_on ‘x'’ >- (
   fs [bir_state_t_component_equality]
  )
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtB_def] >>
 Cases_on ‘bir_state_is_terminated (bir_exec_stmt_assert b state)’ >> (
  fs [bir_exec_stmt_assert_def] >>
  Cases_on ‘option_CASE (bir_eval_exp b state.bst_environ) NONE bir_dest_bool_val’ >> (
   fs [bir_state_set_typeerror_def, bir_state_t_component_equality]
  ) >>
  Cases_on ‘x’ >> (
   fs [bir_state_t_component_equality]
  )
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtB_def] >>
 Cases_on ‘bir_state_is_terminated (bir_exec_stmt_assume b state)’ >> (
  fs [bir_exec_stmt_assume_def] >>
  Cases_on ‘option_CASE (bir_eval_exp b state.bst_environ) NONE bir_dest_bool_val’ >> (
   fs [bir_state_set_typeerror_def, bir_state_t_component_equality]
  ) >>
  Cases_on ‘x’ >> (
   fs [bir_state_t_component_equality]
  )
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtB_def, bir_exec_stmt_observe_def] >>
 Cases_on ‘option_CASE (bir_eval_exp b state.bst_environ) NONE bir_dest_bool_val’ >> (
  fs [bir_state_set_typeerror_def, bir_state_is_terminated_def, bir_state_t_component_equality] >>
  Cases_on ‘x’ >> (
   fs [] >>
   Cases_on ‘EXISTS IS_NONE (MAP (λe. bir_eval_exp e state.bst_environ) l)’ >> (
    FULL_SIMP_TAC std_ss [] >>
    fs [bir_state_set_typeerror_def, bir_state_is_terminated_def, bir_state_t_component_equality]
   )
  ) >>
  Cases_on ‘state.bst_status ≠ BST_Running’ >> (
   fs [bir_state_t_component_equality]
  )
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtB_def, bir_exec_stmt_fence_def] >>
 Cases_on ‘bir_state_is_terminated state’ >> (
  fs [bir_state_t_component_equality]
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtE_def, bir_exec_stmt_jmp_def] >>
 Cases_on ‘bir_eval_label_exp b state.bst_environ’ >> (
  fs [bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def]
 ) >- (
  fs [bir_state_t_component_equality]
 ) >>
 Cases_on ‘MEM x (bir_labels_of_program prog)’ >> (
  fs [bir_block_pc_def, bir_state_t_component_equality]
 ),

 fs [bir_exec_stmt_def, bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
 Cases_on ‘option_CASE (bir_eval_exp b state.bst_environ) NONE bir_dest_bool_val’ >> (
  fs [bir_state_set_typeerror_def, bir_exec_stmt_jmp_def]
 ) >- (
  fs [bir_state_t_component_equality]
 ) >>
 Cases_on ‘x’ >| [
  Cases_on ‘bir_eval_label_exp b0 state.bst_environ’ >> (
   fs [bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def]
  ) >- (
   fs [bir_state_t_component_equality]
  ) >>
  Cases_on ‘MEM x (bir_labels_of_program prog)’ >> (
   fs [bir_block_pc_def, bir_state_t_component_equality]
  ),

  Cases_on ‘bir_eval_label_exp b1 state.bst_environ’ >> (
   fs [bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def]
  ) >- (
   fs [bir_state_t_component_equality]
  ) >>
  Cases_on ‘MEM x (bir_labels_of_program prog)’ >> (
   fs [bir_block_pc_def, bir_state_t_component_equality]
  )
 ],

 fs [bir_exec_stmt_def, bir_exec_stmtE_def, bir_exec_stmt_halt_def] >>
 Cases_on ‘bir_eval_exp b state.bst_environ’ >> (
  fs [bir_state_set_typeerror_def, bir_state_t_component_equality]
 )
]
QED


val _ = export_theory();
