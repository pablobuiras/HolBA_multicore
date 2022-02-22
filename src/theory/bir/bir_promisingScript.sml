open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
open listRangeTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;

val _ = new_theory "bir_promising";

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val _ = Datatype‘
  mem_msg_t = <|
    loc : bir_val_t;
    val : bir_val_t;
    cid : num
    |>
’;

(* UNUSED
val _ = Datatype‘
  mem_t = <|
    bmst_lock        : num option;
    bmst_counter     : num;
    bmst_storebuffer : mem_msg_t list;
    |>
’;
*)

(* Type of instruction and their arguments. *)
val _ = Datatype‘
  bir_statement_type_t =
  | BirStmt_Read bir_var_t bir_exp_t ((bir_cast_t # bir_immtype_t) option) bool
  | BirStmt_Write bir_exp_t bir_exp_t bool
  | BirStmt_Expr bir_var_t bir_exp_t
  | BirStmt_Fence bir_memop_t bir_memop_t
  | BirStmt_Branch bir_exp_t bir_label_exp_t bir_label_exp_t
  | BirStmt_Generic ('a bir_stmt_t)
  | BirStmt_None
’;

(* Default value of memory *)
val mem_default_value_def = Define ‘
  mem_default_value = BVal_Imm (Imm64 0w)
’;

(* Returns the SOME value of the message if the location matches, else NONE. *)
val mem_read_aux_def = Define‘
   mem_read_aux l NONE = NONE
/\ mem_read_aux l (SOME msg) = if msg.loc = l then SOME msg.val else NONE
’;

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
  mem_read M l 0 = SOME mem_default_value
∧ mem_read M l (SUC t) = mem_read_aux l (oEL t M)
’;

(* Returns if all pairs (timestamp * message) satisfies P. *)
val mem_every_def = Define‘
  mem_every P M = EVERY P (ZIP (M, [1 .. LENGTH M]))
’;


(* Returns pairs (timestamp * message) satisfying P *)
val mem_filter_def = Define‘
  mem_filter P M = FILTER P (ZIP (M, [1 .. LENGTH M]))
’;

Theorem mem_every_rwr:
  ∀P M.
    mem_every P M = EVERY P (GENLIST (\t. EL t M, t + 1) (LENGTH M))
Proof
  fs [mem_every_def, listRangeINC_def, ZIP_GENLIST]
QED

Theorem mem_filter_rwr:
  ∀P M.
    mem_filter P M = FILTER P (GENLIST (\t. EL t M, t + 1) (LENGTH M))
Proof
  fs [mem_filter_def, listRangeINC_def, ZIP_GENLIST]
QED

(* Returns timestamps of messages with location l. *)
val mem_timestamps_def = Define‘
  mem_timestamps l M = MAP SND (mem_filter (λ(m, t). m.loc = l) M)
’;

(* The atomic predicate from promising-semantics. *)
val mem_atomic_def = Define‘
  mem_atomic M l cid t_r t_w =
  (((EL (t_r - 1) M).loc = l ∨ t_r = 0)⇒
     mem_every (λ(m,t'). (t_r < t' ∧ t' < t_w ∧ m.loc = l) ⇒ m.cid = cid) M)
’;

(* Checks
 * (∀t'. ((t:num) < t' ∧ t' ≤ (MAX ν_pre (s.bst_coh l))) ⇒ (EL t' M).loc ≠ l)
 * letting t_max = (MAX v_pre (s.bst_coh l))
 *)
val mem_readable_def = Define‘
  mem_readable M l t_max t =
  mem_every (λ(m,t'). (t < t' ∧ t' ≤ t_max) ⇒ m.loc ≠ l) M
’;

(* Note that this currently does not take into account ARM *)
val mem_read_view_def = Define‘
  mem_read_view (f:fwdb_t) t = if f.fwdb_time = t ∧ ~f.fwdb_xcl then f.fwdb_view else t
’;

val bir_eval_view_of_exp = Define‘
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
’;

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
val bir_eval_exp_view_def = Define‘
  bir_eval_exp_view exp env viewenv =
  (bir_eval_exp exp env, bir_eval_view_of_exp exp viewenv)
’;

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
val get_read_args_def = Define`
  (get_read_args (BExp_Load mem_e a_e en ty) =
     SOME (a_e, NONE)) /\
  (get_read_args (BExp_Cast cast_ty load_e imm_ty) =
   case get_read_args load_e of
   | SOME (a_e, NONE) => SOME (a_e, SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_read_args _ = NONE)
`;


(* Obtains an option type that contains the store arguments
 * needed to apply the fulfil rule *)
val get_fulfil_args_def = Define`
  (get_fulfil_args (BExp_IfThenElse cond_e e1 e2) = get_fulfil_args e1) /\
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) =
   SOME (a_e, v_e)) /\
  (get_fulfil_args _ = NONE)
`;

Theorem get_read_fulfil_args_exclusive:
∀e.
  (IS_SOME (get_read_args e) ⇒ get_fulfil_args e = NONE)
∧ (IS_SOME (get_fulfil_args e) ⇒ get_read_args e = NONE)
Proof
  Cases >>
  fs [get_read_args_def, get_fulfil_args_def]
QED

val get_xclb_view_def = Define`
  get_xclb_view (SOME xclb) = xclb.xclb_view
∧ get_xclb_view NONE = 0
`;

val fulfil_atomic_ok_def = Define`
  (fulfil_atomic_ok M l cid s tw =
   case s.bst_xclb of
   | SOME xclb =>
     ((EL (xclb.xclb_time-1) M).loc = l ∨ (xclb.xclb_time = 0)) ==>
       (!t'. (xclb.xclb_time < t'
             /\ t' < tw
             /\ (EL (t'-1) M).loc = l) ==> (EL (t'-1) M).cid = cid)
   | NONE => F)
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
val is_xcl_read_def = Define‘
  is_xcl_read p pc a_e =
    case bir_get_current_statement p (bir_pc_next pc) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
                       var BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))))) => var = a_e
     | _ => F
’;

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

Theorem is_xcl_read_is_xcl_write:
  !p s a_e. is_xcl_read p s a_e /\ is_xcl_write p s ==> F
Proof
  REWRITE_TAC[is_xcl_write_thm,is_xcl_read_thm]
  >> rpt strip_tac
  >> fs[]
  >> cheat
QED


val bir_get_stmt_def = Define‘
  bir_get_stmt p pc =
  case bir_get_current_statement p pc of
  | SOME (BStmtB (BStmt_Assign var e)) =>
      (case get_read_args e of
       | SOME (a_e, cast_opt) => BirStmt_Read var a_e cast_opt (is_xcl_read p pc a_e)
       | NONE =>
           (case get_fulfil_args e of
            | SOME (a_e, v_e) => BirStmt_Write a_e v_e (is_xcl_write p pc)
            | NONE => BirStmt_Expr var e))
  | SOME (BStmtB (BStmt_Fence K1 K2)) => BirStmt_Fence K1 K2
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) => BirStmt_Branch cond_e lbl1 lbl2
  | SOME stmt => BirStmt_Generic stmt
  | NONE => BirStmt_None
’;


Theorem bir_get_stmt_read:
∀p pc stmt var e a_e cast_opt xcl.
 (bir_get_stmt p pc = BirStmt_Read var a_e cast_opt xcl) ⇔
 (?e. bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 ∧ get_read_args e = SOME (a_e, cast_opt)
 ∧ is_xcl_read p pc a_e = xcl)
Proof
  gvs [bir_get_stmt_def,AllCaseEqs(),
       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem bir_get_stmt_write:
∀p pc stmt a_e v_e xcl.
 (bir_get_stmt p pc = BirStmt_Write a_e v_e xcl) ⇔
 (∃var e. bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 ∧ get_fulfil_args e = SOME (a_e, v_e)
 ∧ is_xcl_write p pc = xcl)
Proof
  rw [bir_get_stmt_def,AllCaseEqs()] >>
  eq_tac >>
  rw [get_read_fulfil_args_exclusive]
QED

Theorem bir_get_stmt_expr:
∀p pc stmt var e a_e cast_opt xcl.
 (bir_get_stmt p pc = BirStmt_Expr var e) ⇔
 (bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 ∧ get_read_args e = NONE
 ∧ get_fulfil_args e = NONE)
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_fence:
∀p pc stmt K1 K2.
 (bir_get_stmt p pc = BirStmt_Fence K1 K2) ⇔
 bir_get_current_statement p pc = SOME (BStmtB (BStmt_Fence K1 K2))
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_branch:
∀p pc stmt cond_e lbl1 lbl2.
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

Theorem bir_get_stmt_none:
∀p pc stmt.
 (bir_get_stmt p pc = BirStmt_None) ⇔
 bir_get_current_statement p pc = NONE
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

(* TODO: "Generalising variable "ν_pre" in clause #0 (113:1-131:23)"? *)
(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v a_e xcl M l (t:num) v_pre v_post v_addr var new_env cid opt_cast.
   bir_get_stmt p s.bst_pc = BirStmt_Read var a_e opt_cast xcl
 (* NOTE: The fact that get_read_args is not NONE means also
  *       that the expression e constitutes a load operation *)
 (* If next statement is the dummy exclusive-load statement,
  * we are dealing with an exclusive load *)
 /\ xcl = is_xcl_read p s.bst_pc a_e
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 ∧ mem_read M l t = SOME v
 ∧ v_pre = MAX v_addr s.bst_v_rNew
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX ν_pre (s.bst_coh l))) ⇒ (EL t' M).loc ≠ l)
 ∧ v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 (* TODO: Update viewenv by v_addr or v_post? *)
 ∧ s' = s with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
                  bst_environ := new_env;
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_xclb := if xcl
                              then SOME <| xclb_time := t; xclb_view := v_post |>
                              else s.bst_xclb;
                  bst_pc := if xcl
                            then (bir_pc_next o bir_pc_next) s.bst_pc
                            else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M [] s')
/\ (* exclusive-failure *)
(!p s s' M a_e v_e cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e T
 /\  SOME new_env = xclfail_update_env p s
 /\  SOME new_viewenv = xclfail_update_viewenv p s
 /\  s' = s with <| bst_environ := new_env;
                    bst_viewenv := new_viewenv;
                    bst_xclb := NONE;
                    bst_pc := (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc |>
 ==>
clstep p cid s M [] s')
/\ (* fulfil *)
(!p s s' M v a_e xcl l (t:num) v_pre v_post v_addr v_data v_e cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
 /\ (xcl ==> fulfil_atomic_ok M l cid s t)
 /\ MEM t s.bst_prom
 /\ EL t M = <| loc := l; val := v; cid := cid  |>
 /\ t < LENGTH M
 (* TODO: Use get_xclb_view or separate conjunct to extract option type? *)
 /\ v_pre = MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
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
  clstep p cid s M [t] s')
/\ (* fence *)
(!p s s' K1 K2 M cid v.
   bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2
   /\ v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                     bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
                     bst_pc updated_by bir_pc_next |>
==>
  clstep p cid s M [] s')
/\ (* branch (conditional jump) *)
(!p s s' M cid v oo s2 v_addr cond_e lbl1 lbl2 stm.
   bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2
    /\ stm = BStmtE (BStmt_CJmp cond_e lbl1 lbl2)
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
    /\ bir_exec_stmt p stm s = (oo,s2)
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>
==>
  clstep p cid s M [] s')
/\ (* register-to-register operation *)
(!p s s' M cid v v_val e.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e
 /\ (SOME v, v_val) = bir_eval_exp_view e s.bst_environ s.bst_viewenv
 /\ NONE = get_read_args e
 /\ NONE = get_fulfil_args e
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 /\ s' = s with <| bst_environ := new_env;
                   bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                   bst_pc      updated_by bir_pc_next |>
==> clstep p cid s M [] s')
/\ (* Other BIR single steps *)
(!p s s' M cid stm oo.
   bir_get_stmt p s.bst_pc = BirStmt_Generic stm
    /\ bir_exec_stmt p stm s = (oo,s')
==>
  clstep p cid s M [] s')
`;


(* core steps *)
val (bir_cstep_rules, bir_cstep_ind, bir_cstep_cases) = Hol_reln`
(* execute *)
(!p cid s M s' prom.
  clstep p cid s M prom s'
==>
  cstep p cid s M prom s' M)

/\ (* promise *)
(!p cid s M s' t msg.
   (msg.cid = cid
   /\ t = LENGTH M + 1
   /\ s' = s with bst_prom updated_by (\pr. pr ++ [t]))
==>
  cstep p cid s M [t] s' (M ++ [msg]))
`;

(* core steps seq *)
val (bir_cstep_seq_rules, bir_cstep_seq_ind, bir_cstep_seq_cases) = Hol_reln`
(* seq *)
(!p cid s M s'.
  clstep p cid s M ([]:num list) s'
==>
  cstep_seq p cid (s, M) (s', M))

/\ (* write *)
(!p cid s M s' s'' M' t.
  (cstep p cid s M [t] s' M'
  /\ clstep p cid s' M' [t] s'')
==>
  cstep_seq p cid (s, M) (s'', M'))
`;

val cstep_seq_rtc_def = Define`cstep_seq_rtc p cid = (cstep_seq p cid)^*`

(*
 * properties about cstep, clstep, cstep_seq
 *)

(* the timestamp of a fulfil is coupled to the fulfiled core *)

Theorem cstep_fulfil_to_memory:
  !p cid s M t s'. cstep p cid s M [t] s' M
  ==> t < LENGTH M /\ (EL t M).cid = cid
Proof
  fs[bir_cstep_cases,bir_clstep_cases,PULL_EXISTS]
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
  >> gvs[bir_clstep_cases]
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

(* set of promises contains only elements smaller then the memory *)

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
  >> gvs[stmt_generic_step_def,bir_programTheory.bir_exec_stmt_def,pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_programTheory.bir_exec_stmt_halt_def]
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

Theorem clstep_EVERY_LENGTH_bst_prom_inv:
  !p cid s M prom s'. clstep p cid s M prom s'
  /\ EVERY (λx. x <= LENGTH $ M) s.bst_prom
  ==> EVERY (λx. x <= LENGTH $ M) s'.bst_prom
Proof
  rw[bir_clstep_cases]
  >> imp_res_tac is_xcl_read_is_xcl_write >> fs[]
  >- (
    qhdtm_x_assum `EVERY` mp_tac
    >> fs[EVERY_FILTER]
    >> match_mp_tac EVERY_MONOTONIC
    >> fs[]
  )
  >- (drule_all_then assume_tac bir_exec_stmt_BStmtE_BStmt_CJmp_bst_prom_EQ >> fs[])
  >> qmatch_assum_rename_tac `EVERY _ s.bst_prom`
  >> qmatch_goalsub_abbrev_tac `EVERY _ s'.bst_prom`
  >> qsuff_tac `s.bst_prom = s'.bst_prom` >- (rw[] >> gs[])
  >> irule stmt_generic_step_bst_prom_EQ
  >> goal_assum $ drule_at Any
  >> gvs[stmt_generic_step_def,bir_get_stmt_def,AllCaseEqs()]
QED

Theorem clstep_bst_prom_NOT_EQ:
  !p cid s M t s'. clstep p cid s M [t] s' ==> s.bst_prom <> s'.bst_prom
Proof
  rw[bir_clstep_cases,bir_get_stmt_write]
  >> fs[Once EQ_SYM_EQ,FILTER_NEQ_ID]
QED

Theorem clstep_LENGTH_prom:
  !p cid s M prom s'. clstep p cid s M prom s' ==> prom = [] \/ ?t. prom = [t]
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
!p cid st M st'.
  clstep p cid st M [] st' ==> st.bst_prom = st'.bst_prom
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

Theorem cstep_seq_bst_prom_EQ:
  !p cid sM sM'. cstep_seq p cid sM sM'
  /\ EVERY (λx. x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. x <= LENGTH $ SND sM') (FST sM').bst_prom
    /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac bir_cstep_seq_ind
  >> conj_tac >> rpt gen_tac >> strip_tac
  >- (imp_res_tac clstep_bst_prom_EQ >> fs[])
  >> strip_tac >> conj_asm1_tac
  >- (
    pop_assum mp_tac
    >> gvs[bir_cstep_cases,bir_clstep_cases,rich_listTheory.FILTER_APPEND,EVERY_FILTER]
    >> match_mp_tac EVERY_MONOTONIC
    >> fs[]
  )
  >> gvs[bir_clstep_cases,bir_cstep_cases,bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,bir_state_set_typeerror_def,stmt_generic_step_def,bir_exec_stmt_jmp_bst_prom,rich_listTheory.FILTER_APPEND]
  >> fs[Once EQ_SYM_EQ,FILTER_EQ_ID]
  >> qpat_x_assum `EVERY _ _.bst_prom` mp_tac
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem cstep_seq_rtc_bst_prom_EQ:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  /\ EVERY (λx. x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. x <= LENGTH $ SND sM') (FST sM').bst_prom
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
    ~?cid p s i bl.
     FLOOKUP cores cid = SOME (Core cid p s)
     /\ s.bst_pc.bpc_index <> 0
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, bl)
     /\ bl.bb_atomic = T
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
    /\ cstep p cid s M prom s' M'
    /\ is_certified p cid s' M')
==>
   parstep cid cores M (FUPDATE cores (cid, Core cid p s')) M')
`;

(* Core-local execution *)
val eval_clstep_read_def = Define‘
  eval_clstep_read s M var a_e xcl =
    let
      (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    in
      case l_opt of
	SOME l =>
	let
          v_pre = MAX v_addr s.bst_v_rNew;
	  ts    = FILTER (mem_readable M l (MAX v_pre (s.bst_coh l))) (0::mem_timestamps l M)
	in
	  LIST_BIND ts (\t.
		 let
                   v_opt  = mem_read M l t;
		   v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t);
		 in
		   case v_opt of
		     SOME v =>
		       (case env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ) of
			 SOME new_env =>
			   [s with <| bst_environ := new_env;
                                      bst_viewenv updated_by (λenv. FUPDATE env (var, v_post));
				      bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_post);
				      bst_v_rOld  updated_by (MAX v_post);
				      bst_v_CAP   updated_by (MAX v_addr);
                                      bst_pc      updated_by if xcl
                                                             then (bir_pc_next o bir_pc_next)
                                                             else bir_pc_next;
				      bst_xclb    := if xcl
						     then SOME <| xclb_time := t; xclb_view := v_post |>
						     else s.bst_xclb |>]
		        | _ => [])
		   | _ => [])
      | _ => []
’;

val eval_clstep_xclfail_def = Define‘
  eval_clstep_xclfail p s xcl =
  if xcl then
    (case (xclfail_update_env p s, xclfail_update_viewenv p s) of
    | (SOME new_env, SOME new_viewenv) =>
        [s with <| bst_viewenv := new_viewenv;
                   bst_environ := new_env;
                   bst_xclb    := NONE;
                   bst_pc updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>]
    | _ => [])
  else []
’;

val eval_clstep_fulfil_def = Define‘
  eval_clstep_fulfil p cid s M a_e v_e xcl =
    let
      (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
      (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    in
      case (l_opt,v_opt) of
      | (SOME l, SOME v) =>
          (let
             v_pre = MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
                         (if xcl then get_xclb_view s.bst_xclb else 0);
             ts = FILTER (\t. (EL (t-1) M = <| loc := l; val := v; cid := cid  |>)
                              /\ (MAX v_pre (s.bst_coh l) < t)
                              /\ (xcl ==> ((s.bst_xclb <> NONE) /\
                                             mem_atomic M l cid (THE s.bst_xclb).xclb_time t)))
                         s.bst_prom;
           in
             LIST_BIND ts
                       (\v_post.
                          case (fulfil_update_env p s xcl, fulfil_update_viewenv p s xcl v_post) of
                          | (SOME new_env, SOME new_viewenv) =>
                              [s with <| bst_viewenv := new_viewenv;
                                         bst_environ := new_env;
                                         bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                         bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
                                         bst_v_wOld updated_by MAX v_post;
                                         bst_v_CAP  updated_by MAX v_addr;
                                         bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
                                                                        fwdb_view := MAX v_addr v_data;
                                                                        fwdb_xcl := xcl |>);
                                         bst_pc     updated_by if xcl
                                                               then (bir_pc_next o bir_pc_next o bir_pc_next)
                                                               else bir_pc_next;
                                         bst_xclb := if xcl then NONE else s.bst_xclb |>]
                          | _ => []))
      | (_, _) => []
’;

val eval_clstep_fence_def = Define‘
  eval_clstep_fence s K1 K2 =
  let v = MAX (if is_read K1 then s.bst_v_rOld else 0)
              (if is_write K1 then s.bst_v_wOld else 0)
  in
    [s with <| bst_v_rNew updated_by MAX (if is_read K2 then v else 0);
               bst_v_wNew updated_by MAX (if is_write K2 then v else 0);
               bst_pc     updated_by bir_pc_next |>]
’;

val eval_clstep_branch_def = Define‘
  eval_clstep_branch p s cond_e lbl1 lbl2 =
  let
    stmt = BStmtE (BStmt_CJmp cond_e lbl1 lbl2);
    (sv, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
  in
    case sv of
      SOME v =>
        let (oo,s2) = bir_exec_stmt p stmt s
        in [s2 with <| bst_v_CAP updated_by MAX v_addr |>]
’;

val eval_clstep_exp_def = Define‘
  eval_clstep_exp s var ex =
  case bir_eval_exp_view ex s.bst_environ s.bst_viewenv
  of (SOME val, v_val) =>
       (case env_update_cast64 (bir_var_name var) val (bir_var_type var) (s.bst_environ) of
          SOME new_env =>
            [s with <| bst_environ := new_env;
                       bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                       bst_pc      updated_by bir_pc_next |>]
        | _ => [])
  | _ => []
’;

val eval_clstep_bir_step_def = Define‘
  eval_clstep_bir_step p s stm =
   let (oo,s') = bir_exec_stmt p stm s
   in [s']
’;

val eval_clstep_def = Define‘
  eval_clstep p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl =>
        eval_clstep_read s M var a_e xcl
    | BirStmt_Write a_e v_e xcl =>
        eval_clstep_fulfil p cid s M a_e v_e xcl ++
        eval_clstep_xclfail p s xcl
    | BirStmt_Expr var e =>
        eval_clstep_exp s var e
    | BirStmt_Fence K1 K2 =>
        eval_clstep_fence s K1 K2
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        eval_clstep_branch p s cond_e lbl1 lbl2
    | BirStmt_Generic stm =>
        eval_clstep_bir_step p s stm
    | BirStmt_None => []
’;


(*** Certify execution execution ***)
val eval_certify_def = Define‘
  (
  eval_certify p cid s M 0 =
  NULL s.bst_prom
  ) /\ (
  eval_certify p cid s M (SUC fuel) =
  (NULL s.bst_prom \/
   EXISTS (\s'. eval_certify p cid s' M fuel)
          (eval_clstep p cid s M))
  )
’;

(*** Non-promising-mode execution ***)
val eval_clsteps_def = Define‘
  (
  eval_clsteps 0 cid p s M =
  case s.bst_status of
  | BST_Running => [s]
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  ) /\ (
  eval_clsteps (SUC f) cid p s M =
  case s.bst_status of
  | BST_Running => LIST_BIND (eval_clstep p cid s M)
                             (λs'. eval_clsteps f cid p s' M)
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  )
’;

val eval_clsteps_core_def = Define‘
  eval_clsteps_core fuel (Core cid p s) M =
    MAP (Core cid p) (eval_clsteps fuel cid p s M)
’;

(********* Promising-mode steps ***********)

(* Find promise write step (promise-step + fulfil) *)
Definition eval_fpstep_write_def:
  eval_fpstep_write p cid s M a_e v_e xcl =
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <| val := v; loc := l; cid := cid |>;
           M' = SNOC msg M;
           s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
           v_pre = MAX v_addr $ MAX v_data $ MAX s.bst_v_wNew $ MAX s.bst_v_CAP
                        $ if xcl then get_xclb_view s.bst_xclb else 0;
           v_coh = s.bst_coh l;
           t = SUC (LENGTH M);
         in
           MAP (\s''. (SOME (msg, MAX v_pre v_coh), s''))
               (eval_clstep_fulfil p cid s' M' a_e v_e xcl)
        )
    | _ => []
End

(* Find-promise step *)
Definition eval_fpstep_def:
  eval_fpstep p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl =>
        MAP (\s. (NONE,s)) (eval_clstep_read s M var a_e xcl)
    | BirStmt_Write a_e v_e xcl =>
        (MAP (\s. (NONE,s)) (eval_clstep_fulfil p cid s M a_e v_e xcl)) ++
        (MAP (\s. (NONE,s)) (eval_clstep_xclfail p s xcl)) ++
        (eval_fpstep_write p cid s M a_e v_e xcl)
    | BirStmt_Expr var e =>
        MAP (\s. (NONE,s)) (eval_clstep_exp s var e)
    | BirStmt_Fence K1 K2 =>
        MAP (\s. (NONE,s)) (eval_clstep_fence s K1 K2)
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        MAP (\s. (NONE,s)) (eval_clstep_branch p s cond_e lbl1 lbl2)
    | BirStmt_Generic stm =>
        MAP (\s. (NONE,s)) (eval_clstep_bir_step p s stm)
    | BirStmt_None => []
End


(* Find-promise steps *)
Definition eval_fpsteps_def:
  (
  eval_fpsteps 0 t p cid s M promises =
  if NULL s.bst_prom then promises else []
  ) ∧ (
  eval_fpsteps (SUC f) t p cid s M promises =
  case s.bst_status of
  | BST_Running =>
      LIST_BIND (eval_fpstep p cid s M)
                (λ(msg_opt,s').
                   case msg_opt of
                   | SOME (msg, t_min) =>
                       (let promises' = if t_min < t then msg::promises else promises in
                          eval_fpsteps f t p cid s' (SNOC msg M) promises')
                   | NONE => eval_fpsteps f t p cid s' M promises)
  | BST_Halted _ => if NULL s.bst_prom then promises else []
  | _ => []
  )
End

(* Find-promise steps on a core *)
Definition eval_fpsteps_core_def:
  eval_fpsteps_core fuel t (Core cid p s) M =
  eval_fpsteps fuel t p cid s M []
End

(* Find promise all promises *)
Definition eval_find_promises_def:
  eval_find_promises fuel (cores, M) =
  let t = SUC (LENGTH M) in
  LIST_BIND cores (λcore. eval_fpsteps_core fuel t core M)
End

(* Make a promise step *)
Definition eval_make_promise_def:
  eval_make_promise ((Core cid p s)::cores,M) msg =
  if msg.cid = cid then
    let
      M' = SNOC msg M;
      t = LENGTH M';
      s' = s with <| bst_prom updated_by (CONS t) |>;
    in ((Core cid p s')::cores, M')
  else
    let
      (cores', M') = eval_make_promise (cores, M) msg;
    in ((Core cid p s)::cores', M')
End

(* Promise-mode step *)
Definition eval_pmstep_def:
  eval_pmstep fuel cM =
  MAP (eval_make_promise cM)
      (eval_find_promises fuel cM)
End

(* Check if core has finished execution and is certified *)
Definition is_final_core_def:
  is_final_core (Core cid p s) =
  case s.bst_status of
  | BST_Halted _ => NULL s.bst_prom
  | _ => F
End

(* Optimized atomic *)
Definition mem_atomicO1_def:
  (
  mem_atomicO1 M l cid F xclb_opt t_w = T
  ) ∧ (
  mem_atomicO1 M l cid T NONE t_w = F
  ) ∧ (
    mem_atomicO1 M l cid T (SOME xclb) t_w =
    (let t_r = xclb.xclb_time in
       ((EL (t_r-1) M).loc = l ∨ t_r = 0) ⇒
       mem_every (λ(msg,t'). t_r < t' ∧ t' < t_w ∧ msg.loc = l ⇒ msg.cid = cid) M)
    )
End

(* Optimized fulfil *)
Definition eval_clstep_fulfilO1_def:
  eval_clstep_fulfilO1 p cid s M a_e v_e xcl =
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <| val := v; loc := l; cid := cid |>;
           v_pre = MAX v_addr (MAX v_data (MAX s.bst_v_wNew (MAX s.bst_v_CAP
                        (if xcl then get_xclb_view s.bst_xclb else 0))));
           (* Candidate t's *)
           ts = FILTER (\t. (EL (t-1) M = msg) /\
                            (MAX v_pre (s.bst_coh l) < t) /\
                            (mem_atomicO1 M l cid xcl s.bst_xclb t)) s.bst_prom;
           (* Smallest ts *)
           t = FILTER (λt. EVERY (λt'. t ≤ t') ts) ts;
         in
           LIST_BIND t
                     (λv_post.
                        case (fulfil_update_env p s xcl, fulfil_update_viewenv p s xcl v_post) of
                        | (SOME new_env, SOME new_viewenv) =>
                            [s with <| bst_viewenv := new_viewenv;
                                       bst_environ := new_env;
                                       bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                       bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
                                       bst_v_wOld updated_by MAX v_post;
                                       bst_v_CAP  updated_by MAX v_addr;
                                       bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
                                                                      fwdb_view := MAX v_addr v_data;
                                                                      fwdb_xcl := xcl |>);
                                       bst_pc     updated_by if xcl
                                                             then (bir_pc_next o bir_pc_next o bir_pc_next)
                                                             else bir_pc_next;
                                       bst_xclb := if xcl then NONE else s.bst_xclb |>]
                        | _ => []
                     )
        )
    | _ => []
End

(* Optimized xclfail *)
Definition eval_clstep_xclfailO1_def:
  eval_clstep_xclfailO1 p s T =
    (case (xclfail_update_env p s, xclfail_update_viewenv p s) of
    | (SOME new_environ, SOME new_viewenv) =>
        [s with <| bst_environ := new_environ;
                   bst_viewenv := new_viewenv;
                   bst_xclb    := NONE;
                   bst_pc updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>]
    | _ => [])
 ∧
 eval_clstep_xclfailO1 p s F = []
End

(* Optimized clstep *)
Definition eval_clstepO1_def:
  eval_clstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl =>
        eval_clstep_read s M var a_e xcl
    | BirStmt_Write a_e v_e xcl =>
        eval_clstep_fulfilO1 p cid s M a_e v_e xcl ++
        eval_clstep_xclfailO1 p s xcl
    | BirStmt_Expr var e =>
        eval_clstep_exp s var e
    | BirStmt_Fence K1 K2 =>
        eval_clstep_fence s K1 K2
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        eval_clstep_branch p s cond_e lbl1 lbl2
    | BirStmt_Generic stm =>
        eval_clstep_bir_step p s stm
    | BirStmt_None => []
End

(* Optimized clsteps *)
val eval_clstepsO1_def = Define‘
  (
  eval_clstepsO1 0 cid p s M =
  case s.bst_status of
  | BST_Running => [s]
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  ) /\ (
  eval_clstepsO1 (SUC f) cid p s M =
  case s.bst_status of
  | BST_Running => LIST_BIND (eval_clstepO1 p cid s M)
                             (λs'. eval_clstepsO1 f cid p s' M)
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  )
’;

val eval_clsteps_coreO1_def = Define‘
  eval_clsteps_coreO1 fuel (Core cid p s) M =
    MAP (Core cid p) (eval_clstepsO1 fuel cid p s M)
’;

(* Find promise write step (promise-step + fulfil) *)
Definition eval_fpstep_writeO1_def:
  eval_fpstep_writeO1 p cid s M a_e v_e xcl =
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <| val := v; loc := l; cid := cid |>;
           M' = SNOC msg M;
           s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
           v_pre = MAX v_addr (MAX v_data (MAX s.bst_v_wNew (MAX s.bst_v_CAP
                        (if xcl then get_xclb_view s.bst_xclb else 0))));
           v_coh = s.bst_coh l;
           t = SUC (LENGTH M);
         in
           MAP (\s''. (SOME (msg, MAX v_pre v_coh), s''))
               (eval_clstep_fulfilO1 p cid s' M' a_e v_e xcl)
        )
    | _ => []
End

(* Find promise step *)
Definition eval_fpstepO1_def:
  eval_fpstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl =>
        MAP (\s. (NONE,s)) (eval_clstep_read s M var a_e xcl)
    | BirStmt_Write a_e v_e xcl =>
        (MAP (\s. (NONE,s)) (eval_clstep_fulfilO1 p cid s M a_e v_e xcl)) ++
        (MAP (\s. (NONE,s)) (eval_clstep_xclfailO1 p s xcl)) ++
        (eval_fpstep_writeO1 p cid s M a_e v_e xcl)
    | BirStmt_Expr var e =>
        MAP (\s. (NONE,s)) (eval_clstep_exp s var e)
    | BirStmt_Fence K1 K2 =>
        MAP (\s. (NONE,s)) (eval_clstep_fence s K1 K2)
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        MAP (\s. (NONE,s)) (eval_clstep_branch p s cond_e lbl1 lbl2)
    | BirStmt_Generic stm =>
        MAP (\s. (NONE,s)) (eval_clstep_bir_step p s stm)
    | BirStmt_None => []
End

(* Find promise steps *)
Definition eval_fpstepsO1_def:
  (
  eval_fpstepsO1 0 t p cid s M promises =
  if NULL s.bst_prom then promises else []
  ) ∧ (
  eval_fpstepsO1 (SUC f) t p cid s M promises =
  case s.bst_status of
  | BST_Running =>
      LIST_BIND (eval_fpstepO1 p cid s M)
                (λ(msg_opt,s').
                   case msg_opt of
                   | SOME (msg, t_min) =>
                       (let promises' = if t_min < t then msg::promises else promises in
                          eval_fpstepsO1 f t p cid s' (SNOC msg M) promises')
                   | NONE => eval_fpstepsO1 f t p cid s' M promises)
  | BST_Halted _ => if NULL s.bst_prom then promises else []
  | _ => []
  )
End

(* Find promise steps on a core *)
Definition eval_fpsteps_coreO1_def:
  eval_fpsteps_coreO1 fuel t (Core cid p s) M =
  eval_fpstepsO1 fuel t p cid s M []
End

(* Find all next promises-steps *)
Definition eval_find_promisesO1_def:
  eval_find_promisesO1 fuel (cores, M) =
  let t = SUC (LENGTH M) in
  LIST_BIND cores (λcore. eval_fpsteps_coreO1 fuel t core M)
End

(* Make a promise step *)
Definition eval_make_promiseO1_def:
  eval_make_promiseO1 ((Core cid p s)::cores,M) msg =
  if msg.cid = cid then
    let
      M' = SNOC msg M;
      t = LENGTH M';
      s' = s with <| bst_prom updated_by (CONS t) |>;
    in ((Core cid p s')::cores, M')
  else
    let
      (cores', M') = eval_make_promiseO1 (cores, M) msg;
    in ((Core cid p s)::cores', M')
End

(* Promise-mode step *)
Definition eval_pmstepO1_def:
  eval_pmstepO1 fuel cM =
  MAP (eval_make_promiseO1 cM)
      (eval_find_promisesO1 fuel cM)
End

(********************** Example ***********************)

val core1_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
     (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
      (BExp_Const (Imm64 1w)));
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Const (Imm64 2w))) ]
    ;
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val core2_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "x1" (BType_Imm Bit64))
                  (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
                   Bit8);
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Den (BVar "x1" (BType_Imm Bit64))));
                   ];
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val set_env1_def = Define‘
      set_env1 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env; bst_prom := []|>
’;
val set_env2_def = Define‘
      set_env2 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env |>
’;


val core1_st = “set_env1 (bir_state_init ^core1_prog)”;
val core2_st = “set_env2 (bir_state_init ^core2_prog)”;

(* core definitions *)
val cores = “[(Core 0 ^core1_prog ^core1_st);
              (Core 1 ^core2_prog ^core2_st)]”;

val term_EVAL = rand o concl o EVAL;

val pmstep = term_EVAL “eval_pmstep 8 (^cores, [])”;
val pmstepO1 = term_EVAL “eval_pmstepO1 8 (^cores, [])”;
val equivalent = term_EVAL “^pmstep = ^pmstepO1”
val _ = export_theory();
