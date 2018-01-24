open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

load "pairLib";

val _ = new_theory "bir_wp";

(* Helper theorems *)
val bir_mk_bool_val_true_thm = prove(``!v1.
(bir_mk_bool_val v1 = bir_val_true) = v1``, 
RW_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF, 
	       bir_val_false_def, bir_val_true_def, word1_distinct]
);

(* Theorems to check bir_is_bool_exp_env *)
(* Conditional rewrite *)
val bir_is_bool_exp_env_GSYM = prove(``
!env e. bir_is_bool_exp e ==>
 ((bir_env_vars_are_initialised env (bir_vars_of_exp e)) =
 bir_is_bool_exp_env env e)
``, RW_TAC std_ss [bir_is_bool_exp_env_def]
);

val bir_is_bool_exp_GSYM = prove(``
!ex . (type_of_bir_exp ex = SOME BType_Bool) = (bir_is_bool_exp ex)
``, RW_TAC std_ss [BType_Bool_def,GSYM bir_is_bool_exp_def]
);

val bir_env_vars_are_initialised_INTRO = prove(``
! e ope e1 e2 .bir_env_vars_are_initialised e
        (bir_vars_of_exp (BExp_BinExp ope e1 e2)) ==>
  ((bir_env_vars_are_initialised e (bir_vars_of_exp e1)) /\
   (bir_env_vars_are_initialised e (bir_vars_of_exp e2)))
``,
  REPEAT STRIP_TAC >>
  RW_TAC std_ss [bir_is_bool_exp_env_REWRS,
		bir_is_bool_exp_env_def] >>
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def,
		       bir_env_vars_are_initialised_UNION]
);

val bir_is_bool_env_exp_INTRO = prove(``
! env ope e1 e2 .
(bir_is_bool_exp_env env (BExp_BinExp ope e1 e2)) ==>
((bir_is_bool_exp_env env e1) /\ (bir_is_bool_exp_env env e2))
``,
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS]
);

(* Add type condition *)
(* eval({e1/var}ex, en) = eval(ex, {eval(e1, en)/var} en)*)
val bir_eval_exp_subst1_env = prove(
``
!ex en var ty e1.
(?r. (bir_env_lookup var (BEnv en)) = SOME (ty, r)) ==>
(
  bir_eval_exp ex (BEnv (en |+ (var,ty,SOME (bir_eval_exp e1 (BEnv en))))) =
  bir_eval_exp (bir_exp_subst1 (BVar var ty) e1 ex) (BEnv en)
)
``,
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Induct_on `ex` >>
( REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_exp_subst1_REWRS]
) >>
 (* Case not handled: BExp_Den *)
Cases_on `b = BVar var ty` >-
(RW_TAC std_ss [bir_env_read_def, bir_var_name_def, bir_env_lookup_def] >>
 EVAL_TAC) >>
Cases_on `b` >>
Cases_on `var <> s` >-
(FULL_SIMP_TAC std_ss [bir_eval_exp_def] >>
 EVAL_TAC >>
 FULL_SIMP_TAC std_ss []) >>
subgoal `b' <> ty` >- (
  METIS_TAC[]
) >>
 FULL_SIMP_TAC std_ss [bir_env_lookup_def] >>
 EVAL_TAC >>
 RW_TAC std_ss [] >>
 CASE_TAC
);

(* ******************** *)
(* REAL PROOF ON WP *)
(* ******************** *)

(* Definition of pre-post. Notice that we do not have assumption violated *)
val bir_pre_post_def = Define `
bir_pre_post s pre s' post =
  (s.bst_status = BST_Running) ==>
  (bir_is_bool_exp_env s.bst_environ pre) ==>
  (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
  (
    (s'.bst_status = BST_Running) /\
    (bir_is_bool_exp_env s'.bst_environ post) /\
    (bir_eval_exp post (s'.bst_environ) = bir_val_true)
  )
`;

(* Execution of one internal statement *)
    
val bir_exec_stmtB_triple_def = Define `
bir_exec_stmtB_triple stmt pre post =
!s s' obs.
  (bir_env_vars_are_initialised s.bst_environ (bir_vars_of_stmtB stmt) ) ==>
  (bir_exec_stmtB stmt s = (obs, s')) ==>
  (bir_pre_post s pre s' post)
`;


(* (e /\ Q) Assert e {Q} *)
val bir_triple_exec_strmtB_assert_thm = prove(``
! ex post.
  (bir_is_well_typed_stmtB (BStmt_Assert ex)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Assert ex) (BExp_BinExp BIExp_And ex post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,bir_exec_stmt_assert_def] >>
(* Convert all bir_eval_exp in bir_eval_bool_exp *)
IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
REV_FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
(* Infer that ex holds *)
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS, bir_mk_bool_val_true_thm] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF,bir_dest_bool_val_TF] >>
RW_TAC std_ss [] >>
(* Convert  bir_eval_exp of postin bir_eval_bool_exp *)
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_true_thm]
);

(* (e /\ Q) Assume e {Q} *)
val bir_triple_exec_strmtB_assume_thm = prove(``
! ex post.
  (bir_is_well_typed_stmtB (BStmt_Assume ex)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Assume ex) (BExp_BinExp BIExp_And ex post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,bir_exec_stmt_assume_def] >>
(* Convert all bir_eval_exp in bir_eval_bool_exp *)
IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
REV_FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
(* Infer that ex holds *)
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS, bir_mk_bool_val_true_thm] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF,bir_dest_bool_val_TF] >>
RW_TAC std_ss [] >>
(* Convert  bir_eval_exp of postin bir_eval_bool_exp *)
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_true_thm]
);




(* {{e/v}Q}Assign v:=e {Q} *)
val bir_triple_exec_strmtB_assign_thm = prove(``
! v ex post.
  (bir_is_well_typed_stmtB (BStmt_Assign v ex)) ==>
  (bir_is_bool_exp post) ==>
  bir_exec_stmtB_triple (BStmt_Assign v ex) 
   (bir_exp_subst1 v ex post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
		     bir_exec_stmt_assign_def,
		     bir_env_write_def,
		     (GEN_ALL o SYM) bir_env_var_is_declared_ALT_DEF] >>
(* Check that v is declared *)
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def, bir_env_vars_are_initialised_INSERT] >>
REV_FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_weaken] >>
Cases_on `v` >>
Cases_on `s.bst_environ` >>
FULL_SIMP_TAC std_ss [bir_var_name_def, bir_env_update_def, bir_var_type_def] >>
subgoal `type_of_bir_val (bir_eval_exp ex (BEnv f)) = SOME(b)` >-
(
 FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def, bir_var_type_def, type_of_bir_exp_THM_with_init_vars]
) >>
FULL_SIMP_TAC std_ss [LET_DEF, bir_env_var_is_initialised_def] >>
IMP_RES_TAC bir_eval_exp_subst1_env >>
PAT_X_ASSUM ``!ex.p`` (fn thm =>
 ASSUME_TAC (Q.SPECL [`post`, `ex`] thm)) >>
FULL_SIMP_TAC std_ss [bir_var_name_def, bir_var_type_def] >>
RW_TAC std_ss [] >>
(* have atheorem that say that vars of (bir_exp_subst1 (BVar s'' b) ex post) contains *)
(* vars of post minus s'' *)
cheat
);

val bir_env_vars_are_initialised_observe_INSERT = prove(``
! e ec el obf.
(bir_env_vars_are_initialised e
        (bir_vars_of_stmtB (BStmt_Observe ec el obf))) ==>
(bir_env_vars_are_initialised e (bir_vars_of_exp ec))
``,
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def, listTheory.LIST_TO_SET,
   pred_setTheory.IMAGE_INSERT, pred_setTheory.BIGUNION_INSERT,
   bir_env_vars_are_initialised_UNION]
);

(* {Q} Observe ex {Q} *)
val bir_triple_exec_strmtB_observe_thm = prove(``
! ec el obf post.
  (bir_is_well_typed_stmtB (BStmt_Observe ec el obf)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Observe ec el obf)
   post post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* Prove that the observation condition is well typed *)
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,bir_exec_stmt_observe_def,
  bir_is_well_typed_stmtB_def, bir_is_bool_exp_GSYM] >>
IMP_RES_TAC bir_env_vars_are_initialised_observe_INSERT >>
REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_inv] >>
(* Two cases for for the observation condition *)
Cases_on `bir_eval_bool_exp ec s.bst_environ` >>
(FULL_SIMP_TAC std_ss [] >>
 RW_TAC std_ss [])
);


val bir_wp_exec_stmtB_def = Define `
(bir_wp_exec_stmtB (BStmt_Assert ex) post = (BExp_BinExp BIExp_And ex post)) /\
(bir_wp_exec_stmtB (BStmt_Assume ex) post = (BExp_BinExp BIExp_And ex post)) /\
(bir_wp_exec_stmtB (BStmt_Assign v ex) post = (bir_exp_subst1 v ex post)) /\
(bir_wp_exec_stmtB (BStmt_Observe ec el obf) post = post)
`;

val bir_isnot_declare_stmt_def = Define `
bir_isnot_declare_stmt stm = (~(?v . stm = (BStmt_Declare v)))
`;

val bir_wp_exec_stmtB_sound_thm = prove(
``
!stm post.
  (bir_isnot_declare_stmt stm) ==>
  (bir_is_well_typed_stmtB stm) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple stm (bir_wp_exec_stmtB stm post) post
``,
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  Cases_on `stm` >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
			bir_triple_exec_strmtB_assign_thm,
			bir_triple_exec_strmtB_assert_thm,
			bir_triple_exec_strmtB_assume_thm,
			bir_triple_exec_strmtB_observe_thm,
			bir_isnot_declare_stmt_def
		       ] >>
  (RW_TAC std_ss [])
);

val bir_wp_exec_stmtB_bool_thm = prove(
``
!stm post.
  (bir_isnot_declare_stmt stm) ==>
  (bir_is_well_typed_stmtB stm) ==>
  (bir_is_bool_exp post) ==>
  (bir_is_bool_exp (bir_wp_exec_stmtB stm post))
``,
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  Cases_on `stm` >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
			bir_triple_exec_strmtB_assign_thm,
			bir_triple_exec_strmtB_assert_thm,
			bir_triple_exec_strmtB_assume_thm,
			bir_triple_exec_strmtB_observe_thm,
			bir_isnot_declare_stmt_def,
			bir_is_well_typed_stmtB_def,
			bir_is_bool_exp_GSYM,
			bir_is_bool_exp_REWRS
		       ] >>
  (RW_TAC std_ss []) >>
  (FULL_SIMP_TAC std_ss [bir_is_bool_exp_def, bir_exp_subst1_TYPE_EQ])
);


(* Execution of several internal statements *)
val bir_exec_stmtsB_triple_def = Define `
bir_exec_stmtsB_triple stmts pre post =
!s s' obs obs' c c'.
  (EVERY (\stmt. bir_env_vars_are_initialised s.bst_environ (bir_vars_of_stmtB stmt)) stmts) ==>
  (bir_exec_stmtsB stmts (obs, c, s) = (obs', c', s')) ==>
  (bir_pre_post s pre s' post)
`;


val bir_wp_exec_stmtsB_def = Define `
(bir_wp_exec_stmtsB [] post = post) /\
(bir_wp_exec_stmtsB (stmt::stmts) post = 
 bir_wp_exec_stmtB stmt (bir_wp_exec_stmtsB stmts post)
)`;

val bir_wp_exec_stmtsB_bool_thm = prove(``
  !stmts post.
  (EVERY bir_is_well_typed_stmtB stmts) ==>
  (EVERY bir_isnot_declare_stmt stmts) ==>
  (bir_is_bool_exp post) ==>
  (bir_is_bool_exp (bir_wp_exec_stmtsB stmts post))
``,
  REPEAT GEN_TAC >>
  Induct_on `stmts` >-
  (
   FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def, bir_exec_stmtsB_triple_def, bir_exec_stmtsB_def]
  ) >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def, listTheory.EVERY_DEF, bir_wp_exec_stmtB_bool_thm]
);

(* To be cleaned *)
val exec_preserves_initialized_vars_thm = prove(``
!r h st stmts.
(r = bir_exec_stmtB_state (h:'a bir_stmt_basic_t) st) ==>
(EVERY (λstmt:'a bir_stmt_basic_t.
            bir_env_vars_are_initialised st.bst_environ
              (bir_vars_of_stmtB stmt)) stmts) ==>
(EVERY (λstmt.
            bir_env_vars_are_initialised r.bst_environ
              (bir_vars_of_stmtB stmt)) stmts)
``,
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
subgoal `!x. 
 (λstmt:'a bir_stmt_basic_t. bir_env_vars_are_initialised st.bst_environ
	 (bir_vars_of_stmtB stmt)) x ==>
 (λstmt. bir_env_vars_are_initialised r.bst_environ
	 (bir_vars_of_stmtB stmt)) x` >|
[
 GEN_TAC >>
 FULL_SIMP_TAC std_ss [] >>
 DISCH_TAC >>     
 MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_env_vars_are_initialised_ORDER) >>
 Q.EXISTS_TAC `st.bst_environ` >>
 ASM_SIMP_TAC std_ss [bir_exec_stmtB_ENV_ORDER],
 ALL_TAC
] >>
ASSUME_TAC (ISPECL [``
  (λstmt : 'a bir_stmt_basic_t . bir_env_vars_are_initialised st.bst_environ
          (bir_vars_of_stmtB stmt))``,
``(λstmt: 'a bir_stmt_basic_t.bir_env_vars_are_initialised r.bst_environ
     (bir_vars_of_stmtB stmt))``]
		   listTheory.EVERY_MONOTONIC) >>
REV_FULL_SIMP_TAC std_ss []
);

(* I don't think we need is anymore, since we removed assumption violated *)
(* val bir_exec_stmtsB_assumption_violated_thm = prove(`` *)
(* !(q:'a option) fe c r fe' c' st'. *)
(* (bir_exec_stmtsB stmts (OPT_CONS q fe,SUC c,r) = (fe',c',st')) ==> *)
(* (r.bst_status <> BST_Running) ==> *)
(* (st' = r) *)
(* ``, *)
(*   Induct_on `stmts` >| *)
(*  [ *)
(*   REPEAT GEN_TAC >> *)
(*   FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def], *)
(*   REPEAT GEN_TAC >> *)
(*   FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def, bir_state_is_terminated_def] >> *)
(*   REPEAT DISCH_TAC >> *)
(*   FULL_SIMP_TAC std_ss [] *)
(*  ]); *)
  

val bir_wp_exec_stmtsB_sound_thm = prove(``
  !stmts post.
  (EVERY bir_is_well_typed_stmtB stmts) ==>
  (EVERY bir_isnot_declare_stmt stmts) ==>
  (bir_is_bool_exp post) ==>
  (bir_exec_stmtsB_triple stmts (bir_wp_exec_stmtsB stmts post) post)
``,
  REPEAT GEN_TAC >>
  Induct_on `stmts` >-
  (
   FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def, bir_exec_stmtsB_triple_def, bir_exec_stmtsB_def, bir_pre_post_def]
  ) >>
  SIMP_TAC std_ss [bir_exec_stmtsB_triple_def, bir_pre_post_def] >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  FULL_SIMP_TAC std_ss [listTheory.EVERY_DEF] >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def, bir_state_is_terminated_def] >>
  Q.ABBREV_TAC `st1 = bir_exec_stmtB h s` >>
  Cases_on `st1` >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def] >>
  Q.ABBREV_TAC `wp = (bir_wp_exec_stmtsB stmts post)` >>
  (* Handle the first step *)
  ASSUME_TAC (Q.SPECL [`h`, `wp`] bir_wp_exec_stmtB_sound_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bir_wp_exec_stmtsB_bool_thm >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_triple_def] >>
  PAT_X_ASSUM ``!s.p`` (fn thm =>
   ASSUME_TAC (Q.SPECL [`s`, `r`, `q`] thm)) >>
  REV_FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
  (* Inductive hyp *)
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>
  PAT_X_ASSUM ``!st.p`` (fn thm =>
    ASSUME_TAC (Q.SPECL [`r`, `s'`, `OPT_CONS q obs`, `obs'`,
		      `SUC c`, `c':num`] thm)) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  (* prove assumptions of inductive case *)
  subgoal `r = bir_exec_stmtB_state h s` >- (
     FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def]
  ) >>
  IMP_RES_TAC exec_preserves_initialized_vars_thm >>
  FULL_SIMP_TAC std_ss [bir_pre_post_def] 
);

(* Executions of the complete block, including jump *)
val bir_exec_block_jmp_triple_def = Define(`
bir_exec_block_jmp_triple p bl pre post l =
!s l1 c1 s'.
  (bir_env_vars_are_initialised s.bst_environ (bir_vars_of_block bl)) ==>
  (bir_exec_block p bl s = (l1,c1,s')) ==>
  (s.bst_status = BST_Running) ==>
  (bir_is_bool_exp_env s.bst_environ pre) ==>
  (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
  (
    (s'.bst_status = BST_Running) /\
    (bir_is_bool_exp_env s'.bst_environ post) /\
    (bir_eval_exp post (s'.bst_environ) = bir_val_true) /\
    (s'.bst_pc = bir_block_pc l)
  )
`);

val bir_vars_are_initialized_block_then_every_stmts_thm = prove(``
 (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_block bl)) ==>
 (EVERY (λstmt.
    bir_env_vars_are_initialised st.bst_environ
       (bir_vars_of_stmtB stmt)) bl.bb_statements)
``,
  FULL_SIMP_TAC std_ss [bir_vars_of_block_def, listTheory.EVERY_MEM] >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  cheat
);

val bir_exec_block_jmp_triple_wp_thm = prove(``
  !p bl post l.
  (bir_is_well_typed_block bl) ==>
  (EVERY bir_isnot_declare_stmt bl.bb_statements) ==>
  (bir_is_bool_exp post) ==>
  (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l))) ==>
  (MEM l (bir_labels_of_program p)) ==>
  (bir_exec_block_jmp_triple p bl 
    (bir_wp_exec_stmtsB bl.bb_statements post) post l)
``,
 SIMP_TAC std_ss [bir_exec_block_jmp_triple_def] >>
 REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
 Q.ABBREV_TAC `wp = bir_wp_exec_stmtsB bl.bb_statements post` >>
 ASSUME_TAC (Q.SPECL [`bl.bb_statements`,`post`] bir_wp_exec_stmtsB_sound_thm) >>
 (REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def, bir_exec_stmtsB_triple_def]) >>
 FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
 Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,s)` >>
 pairLib.PairCases_on `ns` >>
 FULL_SIMP_TAC std_ss [LET_DEF] >>
 PAT_X_ASSUM ``!x.p`` (fn thm =>
   ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:'a list`, `ns0`, `0:num`, `ns1`]
   thm)) >>
 REV_FULL_SIMP_TAC std_ss [bir_vars_are_initialized_block_then_every_stmts_thm] >>
 subgoal `~(bir_state_is_terminated ns2)` >- (
   FULL_SIMP_TAC std_ss [bir_pre_post_def, bir_state_is_terminated_def]
 ) >>
 FULL_SIMP_TAC std_ss [] >>
 Q.ABBREV_TAC `st2 = (bir_exec_stmtE p (BStmt_Jmp (BLE_Label l)) ns2)` >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_eval_label_exp_def, bir_exec_stmt_jmp_to_label_def] >>
 REV_FULL_SIMP_TAC std_ss [Abbr `st2`] >>
 subgoal `(ns2 with bst_pc := bir_block_pc l).bst_status = ns2.bst_status` >-
 (RW_TAC (srw_ss()) []) >>
 FULL_SIMP_TAC std_ss [] >>
 subgoal `(s'.bst_status = ns2.bst_status) /\
          (s'.bst_environ = ns2.bst_environ)` >-
 (RW_TAC (srw_ss()) []) >>
 (FULL_SIMP_TAC std_ss [bir_state_is_terminated_def, bir_pre_post_def]) >>
 (RW_TAC (srw_ss()) [])
);


(* val bir_is_bool_exp_eval_true_or_false_thm = prove(`` *)
(* ! e env. *)
(* (bir_is_bool_exp_env env e) ==> *)
(* (((bir_dest_bool_val (bir_eval_exp e env)) = (SOME T)) \/ *)
(*  ((bir_dest_bool_val (bir_eval_exp e env)) = (SOME F)) *)
(* ) *)
(* ``, *)
(* REPEAT STRIP_TAC >> *)
(* FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_def, bool2b_def, *)
(* bir_dest_bool_val_def] *)
(* ); *)

val bir_exec_block_cjmp_triple_def = Define `
bir_exec_block_cjmp_triple p bl pre post1 l1 post2 l2 =
!s obs' c1 s'.
  (bir_env_vars_are_initialised s.bst_environ (bir_vars_of_block bl)) ==>
  (bir_exec_block p bl s = (obs',c1,s')) ==>
  (s.bst_status = BST_Running) ==>
  (bir_is_bool_exp_env s.bst_environ pre) ==>
  (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
  (
    (s'.bst_status = BST_Running) /\
    ((
      (bir_is_bool_exp_env s'.bst_environ post1) /\
      (bir_eval_exp post1 (s'.bst_environ) = bir_val_true) /\
      (s'.bst_pc = bir_block_pc l1)
    ) \/ (
      (bir_is_bool_exp_env s'.bst_environ post2) /\
      (bir_eval_exp post2 (s'.bst_environ) = bir_val_true) /\
      (s'.bst_pc = bir_block_pc l2)
    ))
  )
`;


val bir_exec_block_cjmp_triple_wp_thm = prove(``
  !p bl e post1 l1 post2 l2.
  (bir_is_well_typed_block bl) ==>
  (EVERY bir_isnot_declare_stmt bl.bb_statements) ==>
  (bir_is_bool_exp post1) ==>
  (bir_is_bool_exp post2) ==>
  (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))) ==>
  (MEM l1 (bir_labels_of_program p)) ==>
  (MEM l2 (bir_labels_of_program p)) ==>
  (bir_exec_block_cjmp_triple p bl 
    (bir_wp_exec_stmtsB bl.bb_statements  (
    (BExp_BinExp BIExp_And 
		  (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e) post1)
		  (BExp_BinExp BIExp_Or e post2)
		 )
    ))
    post1 l1 post2 l2)
``,
 SIMP_TAC std_ss [bir_exec_block_cjmp_triple_def] >>
 REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
 Q.ABBREV_TAC `q1 = (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e) post1)` >> 
 Q.ABBREV_TAC `q2 = (BExp_BinExp BIExp_Or e post2)` >>
 Q.ABBREV_TAC `post_stmts = (BExp_BinExp BIExp_And q1 q2)` >> 
 Q.ABBREV_TAC `wp = bir_wp_exec_stmtsB bl.bb_statements post_stmts` >>
 (* We use the fact that the WP of internal statements is sound *)
 ASSUME_TAC (Q.SPECL [`bl.bb_statements`,`post_stmts`] bir_wp_exec_stmtsB_sound_thm) >>
 (REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def, bir_exec_stmtsB_triple_def]) >>
 subgoal `bir_is_bool_exp post_stmts` >-
 (
  FULL_SIMP_TAC std_ss [Abbr `q1`, Abbr `q2`, Abbr `post_stmts`,
    bir_is_bool_exp_REWRS, bir_is_well_typed_stmtE_def, BType_Bool_def,
    GSYM bir_is_bool_exp_def]
 ) >>
 (* Open the definition of exec block *)
 FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
 Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,s)` >>
 pairLib.PairCases_on `ns` >>
 FULL_SIMP_TAC std_ss [LET_DEF] >>
 PAT_X_ASSUM ``!x.p`` (fn thm =>
   ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:'a list`, `ns0`, `0:num`, `ns1`]
   thm)) >>
 REV_FULL_SIMP_TAC std_ss [bir_vars_are_initialized_block_then_every_stmts_thm] >>
 subgoal `~(bir_state_is_terminated ns2)` >- (
   FULL_SIMP_TAC std_ss [bir_pre_post_def, bir_state_is_terminated_def]
 ) >>
 FULL_SIMP_TAC std_ss [] >>
 Q.ABBREV_TAC `st2 = (bir_exec_stmtE p (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2)) ns2)` >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
 (* to proove that is_bool e *)
 subgoal `bir_is_bool_exp_env ns2.bst_environ e` >-
 (
  FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
  REV_FULL_SIMP_TAC std_ss [Abbr `post_stmts`, Abbr `q1`, Abbr `q2`] >>
  IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
  IMP_RES_TAC bir_is_bool_env_exp_INTRO
 ) >>
 FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_inv] >>
 REV_FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
 (* Better to have a theorem *)
 (* Proves that since eval_bool (q1 /\ q2) then eval_bool q1 /\ eval_bool q2 *)
 FULL_SIMP_TAC std_ss [Abbr `post_stmts`] >>
 IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
 FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_true_thm,
    bir_eval_bool_exp_BExp_BinExp_REWRS] >>
 Cases_on `bir_eval_bool_exp e ns2.bst_environ` >-
 (
    FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def, bir_eval_label_exp_def, bir_exec_stmt_jmp_to_label_def] >>
    REV_FULL_SIMP_TAC std_ss [Abbr `st2`, bir_state_is_terminated_def] >>
    RW_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [Abbr `q1`] >>
    IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
    subgoal `~(bir_eval_bool_exp (BExp_UnaryExp BIExp_Not e) ns2.bst_environ) ` >-
    (
     FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_UnaryExp_REWRS]
    ) >>
    FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS, bir_eval_bool_exp_INTRO, bir_mk_bool_val_true_thm]
 ) >>
 (* second case when e does not hold *)
 FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def, bir_eval_label_exp_def, bir_exec_stmt_jmp_to_label_def] >>
 REV_FULL_SIMP_TAC std_ss [Abbr `st2`, bir_state_is_terminated_def] >>
 RW_TAC std_ss [] >>
 FULL_SIMP_TAC std_ss [Abbr `q2`] >>
 IMP_RES_TAC bir_is_bool_env_exp_INTRO >>
 FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS, bir_eval_bool_exp_INTRO, bir_mk_bool_val_true_thm]
);


val _ = export_theory();