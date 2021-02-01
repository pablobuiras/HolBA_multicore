open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open bir_mem_coreTheory;
open monadsyntax;
open alistTheory;
open listTheory;

val _ = new_theory "bir_multicore";
(* TODO: Nested Loads and Stores in expressions should be ruled out somehow... *)

val exp_is_load_def = Define `
  (exp_is_load (BExp_Load _ _ _ _) = T) /\
  (exp_is_load _ = F)
`;

(* TODO: Previously this matched against variable name "MEM".
 * For now, we assume that all memories are the main memory *)
val is_mem_def = Define `
  (is_mem (BVar _ (BType_Mem _ _)) = T) /\
  (is_mem _ = F)
`;

val stmt_is_fence_def = Define `
  (stmt_is_fence (BStmtB BStmt_Fence) = T) /\
  (stmt_is_fence _ = F)
`;

val stmt_is_memop_def = Define `
  (stmt_is_memop (BStmtB BStmt_Fence) = T) /\
  (stmt_is_memop (BStmtB (BStmt_Assign var exp)) = ((is_mem var) \/ (exp_is_load exp))) /\
  (stmt_is_memop _ = F)
`;

val pipe_is_empty_def = Define `
  (pipe_is_empty st = (st.bst_inflight = []))
`;


(* ------------------------------------------------------------------------- *)
(*  Nondeterministic step relation with pipelining                           *)
(* ------------------------------------------------------------------------- *)

val next_stmt_def = Define `next_stmt s =
  case s.bst_inflight of
      [] => NONE
    | ((BirInflight t0 stm)::stms) => SOME (t0,stm)
`;

(* Pipelined steps for a single core. *)
(* TODO: Wildcard oo? *)
val (bir_pstep_rules, bir_pstep_ind, bir_pstep_cases) = Hol_reln `
  (* Execution of pending statement in pipeline *)
  (* Only statements which do not assign to, or read from, memory
   * can be directly executed by a single core. *)
  (!p st st' stm oo.
   ((next_stmt st = SOME (t0, stm)) /\
    (bir_exec_stmt p stm s = (oo, st')) /\
    ~(stmt_is_memop stm)
   ) ==>
   pstep p st (st' with bst_inflight updated_by (remove_inflight t0))
  ) /\
  (* Execution of conditional jump *)
  (!p st st' oo exp l1 l2.
   ((pipe_is_empty s) /\
    (bir_get_current_statement p st.bst_pc = SOME (BStmtE (BStmt_CJmp exp l1 l2))) /\
    (bir_exec_stmt p (BStmtE (BStmt_CJmp exp l1 l2)) st = (oo, st'))
   ) ==>
   pstep p st st'
  ) /\
  (* Execution of computed jump *)
  (!p st st' oo lexp.
   ((pipe_is_empty st) /\
    (bir_get_current_statement p st.bst_pc = SOME (BStmtE (BStmt_Jmp (BLE_Exp lexp)))) /\
    (bir_exec_stmt p (BStmtE (BStmt_Jmp (BLE_Exp lexp))) st = (oo, st'))
   ) ==>
   pstep p st st'
  ) /\
  (* Put current statement in pipeline, case within a BIR block *)
  (!p st bstm istm.
   ((bir_get_current_statement p st.bst_pc = SOME (BStmtB bstm)) /\
    (istm = BirInflight (fresh st) (BStmtB bstm))) ==>
   pstep p st (st with <| bst_inflight updated_by (APPEND [istm]);
                          bst_pc updated_by bir_pc_next;
                          bst_counter updated_by (\n:num.n+1) |>)
  ) /\
  (* Put current statement in pipeline, case unconditional jump *)
  (* NOTE: "BStmt_Jmp (BLE_Label lbl)" forbids computed jump targets. *)
  (!p st istm lbl.
   ((bir_get_current_statement p st.bst_pc = SOME (BStmtE (BStmt_Jmp (BLE_Label lbl)))) /\
    (istm = BirInflight (fresh st) (BStmtE (BStmt_Jmp (BLE_Label lbl))))) ==>
   pstep p st (st with <| bst_inflight updated_by (APPEND [istm]);
                          bst_pc := (bir_block_pc lbl);
                          bst_counter updated_by (\n:num.n+1) |>)
  )
`;

val bir_next_fetch_def = Define `bir_next_fetch p s =
  case bir_get_current_statement p s.bst_pc of
      NONE => []
    | SOME stm =>
      [s with <| bst_inflight updated_by (APPEND [BirInflight (fresh s) stm]);
       bst_pc updated_by bir_pc_next; bst_counter updated_by (\n:num.n+1) |>]
`;

val bir_next_exec_def = Define `bir_next_exec p s =
  case next_stmt s of
      NONE => []
    | SOME (t0,stm) => [SND (bir_exec_stmt p stm s) with
                        <| bst_inflight updated_by (remove_inflight t0); |>]
`;

val bir_compute_next_def = Define `bir_compute_next p s =
  bir_next_fetch p s ++ bir_next_exec p s
`;

val bir_compute_steps_defn = Hol_defn "bir_compute_steps" `bir_compute_steps (n:num) p s =
  if n = 0
  then [s]
  else LIST_BIND (bir_compute_next p s) (\s2. bir_compute_steps (n-1) p s2)
`;

(* Defn.tgoal bir_compute_steps_defn *)
val (bir_compute_steps_def, bir_compute_steps_ind) = Defn.tprove (bir_compute_steps_defn,
  WF_REL_TAC `measure (\ (n,_,_). n)`
);

val bir_next_states_def = Define `bir_next_states p s =
  { s2 | pstep p s s2 }
`;

val (is_trace_rules, is_trace_ind, is_trace_cases) = Hol_reln `
  (!p s. is_trace p [s]) /\
  (!p s2 s1 t. ((is_trace p (APPEND t [s1])) /\ (pstep p s1 s2)) ==>
               (is_trace p (APPEND t [s1;s2]))
  )
`;

val bir_traces_def = Define `bir_traces p =
  { t | is_trace p t }
`;

val (is_gen_trace_rules, is_gen_trace_ind, is_gen_trace_cases)  = Hol_reln `
  (!R s. is_gen_trace R [s]) /\
  (!R s2 s1 t . ((is_gen_trace R (APPEND t [s1])) /\ (R s1 s2)) ==>
                (is_gen_trace R (APPEND t [s1;s2]))
  )
`;

val bir_gen_traces_def = Define `gen_traces R =
  { t | is_gen_trace R t }
`;
                   
(* ------------------------------------------------------------------------- *)
(*  Parallel evaluation                                                      *)
(* ------------------------------------------------------------------------- *)

val sys_st_def = Datatype `sys_st =
    core num (string bir_program_t) bir_state_t
  | mem mem_state_t 
`;

val next_is_atomic_def = Define `next_is_atomic p s =
  case (bir_get_program_block_info_by_label p (s.bst_pc.bpc_label)) of
      NONE => F
    | SOME (i,blk) => blk.bb_atomic
`;

val pstep_flush_defn = Hol_defn "pstep_flush" `pstep_flush p s =
  if NULL s.bst_inflight
  then s
  else pstep_flush p (HD (bir_next_exec p s))
`;

(* TODO: Move these to programScript *)
val bir_inflight_ss = rewrites ((type_rws ``:'a bir_inflight_stmt_t``));

val nonempty_pipeline_next_stmt = prove(
``!s. ~NULL s.bst_inflight ==> ~(next_stmt s = NONE)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [next_stmt_def] >>
Cases_on `s.bst_inflight` >| [
  FULL_SIMP_TAC std_ss [NULL_EQ],

  Cases_on `h` >>
  FULL_SIMP_TAC (list_ss++bir_inflight_ss) []
]
);

val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_status_ss = rewrites (type_rws ``:bir_status_t``);

val bir_exec_stmt_inflight_unchanged = store_thm("bir_exec_stmt_inflight_unchanged",
``!p r s.
  (bir_exec_stmt_state p r s).bst_inflight = s.bst_inflight``,

REPEAT STRIP_TAC >>
Cases_on `r` >> Cases_on `b` >> (
  FULL_SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, LET_DEF,
                        bir_exec_stmtB_state_REWRS, bir_exec_stmt_assign_def,
                        bir_exec_stmt_assert_def, bir_exec_stmt_assume_def,
                        bir_exec_stmt_observe_state_def,
                        bir_exec_stmt_fence_state_def,
                        bir_exec_stmtE_def, bir_exec_stmt_jmp_def,
                        bir_exec_stmt_jmp_to_label_def,
                        bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_typeerror_def]
  )
)
);

val bir_next_exec_NONNULL_decreasing = prove(
``!p s.
  ~NULL s.bst_inflight ==>
  LENGTH (HD (bir_next_exec p s)).bst_inflight < LENGTH s.bst_inflight``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [bir_next_exec_def, nonempty_pipeline_next_stmt] >>
IMP_RES_TAC nonempty_pipeline_next_stmt >>
Cases_on `next_stmt s` >| [
  FULL_SIMP_TAC std_ss [],

  Cases_on `x` >>
  FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm] >>
  Cases_on `bir_exec_stmt p r s` >>
  Cases_on `q'` >> (
    FULL_SIMP_TAC std_ss [] >>
    rename1 `s' with bst_inflight updated_by remove_inflight q` >>
    subgoal `s.bst_inflight = s'.bst_inflight` >- (
      subgoal `bir_exec_stmt_state p r s = s'` >- (
	FULL_SIMP_TAC std_ss [bir_exec_stmt_state_def]
      ) >>
      METIS_TAC [bir_exec_stmt_inflight_unchanged]
    ) >>
    FULL_SIMP_TAC (std_ss++bir_state_ss) [remove_inflight_def, listTheory.HD] >>
    irule rich_listTheory.LENGTH_FILTER_LESS >>
    FULL_SIMP_TAC std_ss [next_stmt_def] >>
    Cases_on `s'.bst_inflight` >| [
      FULL_SIMP_TAC std_ss [NULL_EQ],

      Cases_on `h` >>
      REV_FULL_SIMP_TAC (list_ss++bir_inflight_ss) []
    ]
  )
]
);

(* Defn.tgoal pstep_flush_defn *)
val (pstep_flush_def, pstep_flush_ind) = Defn.tprove(pstep_flush_defn,

WF_REL_TAC `measure (\arg. LENGTH ((SND arg).bst_inflight))` >>
FULL_SIMP_TAC std_ss [bir_next_exec_NONNULL_decreasing]
);

(* The write buffer of memory m does not contain any pending writes from
 * core with core ID cid *)
val buffer_is_empty_def = Define`
  (buffer_is_empty m cid =
    (!stmt_cid stmt.
     MEM (stmt_cid, stmt) m.bmst_buffer ==>
     (cid <> stmt_cid)))
`;

val buffer_bypass_read_def = Define`
  (buffer_bypass_read m find_cid find_addr =
     FIND ( \(cid, evt).
             ?evid mem_var addr en value.
            (
             evt = (BEv_Write evid mem_var addr en value)
            ) ==>
           (cid = find_cid /\ addr = find_addr)) (REVERSE m.bmst_buffer)
  )
`;

val lock_held_or_free_def = Define`
  (lock_held_or_free m cid =
    (!cid'. m.bmst_lock = SOME cid' ==> cid = cid'))
`;

val (parstep_rules, parstep_ind, parstep_cases) = Hol_reln`
  (* Obtain a memory core lock for some core.
   * This can only be done if no other core holds the lock,
   * and if in-flight list of the memory does not contain any
   * statement associated with the current core. *)
  (* TODO: This also needs to execute one core step *)
  (!cid p st m m' system.
   (core cid p st) IN system /\
   (mem m) IN system /\
   next_is_atomic p st /\
   m.bmst_lock = NONE /\
   buffer_is_empty m cid /\
   m' = m with <| bmst_lock := SOME cid |> ==>
   parstep system (system DIFF {mem m} UNION {mem m'})
  ) /\
  (* Release a memory core lock.
   * This can only be done if next statement of the core
   * holding the lock is an End statement,
   * and if in-flight list of the memory does not contain any
   * statement associated with the current core.. *)
  (!cid p st m m' system t0 stm.
   (core cid p st) IN system /\
   (mem m) IN system /\
   m.bmst_lock = SOME cid /\
   buffer_is_empty m cid /\
   (next_stmt st = SOME (t0,stm)) /\
   (?end_stmt. stm = BStmtE end_stmt) /\
   m' = m with <| bmst_lock := NONE |> ==>
   parstep system (system DIFF {mem m} UNION {mem m'})
  ) /\
  (* Perform a pipelined step for a single core. *)
  (!cid p st st' system.
   pstep p st st' /\
   (core cid p st) IN system ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'})
  ) /\
  (* Perform a step for a memory - note that with the
   * current definition of memstep this is identical with committing
   * something from the memory in-flight list. *)
  (!m m' system.
   memstep m m' /\
   (mem m) IN system ==>
   parstep system (system DIFF {mem m} UNION {mem m'})
  ) /\
  (* Perform a fence step for a single core and a single memory.
   * This can only be done if in-flight list of the memory does
   * not contain any statement associated with the current core.. *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m m' system system' t0 stm.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    (next_stmt st = SOME (t0, stm)) /\
    (stm = BStmtB BStmt_Fence) /\
    (* This would force the core to flush its in-flight set
    /\ s' = pstep_flush p s *)
    (* This would force a memory to flush its in-flight set
    /\ m' = memflush cid m.bmst_inflight m *)
    (* This forces a memory to have an empty in-flight set *)
    buffer_is_empty m cid /\
    system' = (system DIFF {core cid p st} UNION {core cid p st'})
		DIFF {mem m} UNION {mem m'}) ==>
   parstep system system'
  ) /\
  (* Store to memory (in-flight set)
   * This can only be done if lock is not held by some other core. *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m m' system t0 var mem_ex addr_ex en val_ex addr value.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    (lock_held_or_free m cid) /\
    (* TODO: Implicit assumption that mem_ex is main memory *)
    (next_stmt st = SOME (t0, (BStmtB (BStmt_Assign var (BExp_Store mem_ex addr_ex en val_ex))))) /\
    (?t. var = BVar "MEM" t) /\
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (SOME value = bir_eval_exp val_ex st.bst_environ) /\
    (* TODO: This must not put statements to in-flight set, but rather "writes" where
     * the expressions have been evaluted. *)
    (m' = m with <|bmst_buffer updated_by
		     (APPEND [(cid, BEv_Write (memfresh m) var addr en value)]);
		     bmst_counter updated_by (\n:num. n+1)|>) /\
    (st' = st with bst_inflight updated_by (remove_inflight t0))) ==>
   parstep system ((system DIFF {mem m} UNION {mem m'})
                     DIFF {core cid p st} UNION {core cid p st'})
  ) /\
  (* Load directly from memory
   * This can only be done if the lock is not held by some other core, as well as
   * if the write buffer does not contain a write from the current core to the
   * address that is to be loaded.
   * *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m system t0 var mem_var addr_ex en it addr mem_val value env'.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    (lock_held_or_free m cid) /\
    (next_stmt st = SOME (t0, BStmtB (BStmt_Assign var (BExp_Load (BExp_Den mem_var) addr_ex en it)))) /\
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (buffer_bypass_read m cid addr = NONE) /\
    (* TODO: Implicitly assumed that ex1 actually evaluates to "MEM" *)
    (SOME mem_val = bir_eval_exp (BExp_Den mem_var) m.bmst_environ) /\
    (SOME value = bir_eval_load (SOME mem_val) (SOME addr) en it) /\
    (SOME env' = bir_env_write var value st.bst_environ) /\
    (st' = st with <|bst_environ := env';
                     bst_inflight updated_by (remove_inflight t0)|>)) ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'})) /\
  (* Load from write buffer *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m system t0 var mem_ex addr_ex en it addr wcid wid mem_var value env'.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    (lock_held_or_free m cid) /\
    (next_stmt st = SOME (t0, BStmtB (BStmt_Assign var (BExp_Load mem_ex addr_ex en it)))) /\
    (* TODO: Currently, we don't care about the value of mem_ex, since we only deal
     * with one main memory. *)
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (* TODO: Endianness currently ignored, but must be matched... *)
    (buffer_bypass_read m cid addr = SOME (wcid, BEv_Write wid mem_var addr en value)) /\
    (SOME env' = bir_env_write var value st.bst_environ) /\
    (st' = st with <|bst_environ := env';
                   bst_inflight updated_by (remove_inflight t0)|>)) ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'}))
`;

val par_traces_def = Define `par_traces system =
  gen_traces parstep
`;

val compute_next_par_single_def = Define `compute_next_par_single (core cid p s) m =
  LIST_BIND (bir_compute_next p s) (\s'. [(core cid p s', m)])
`;
val compute_next_par_mem_def = Define `compute_next_par_mem c (mem m) =
  LIST_BIND (mem_compute_next m) (\m'. [(c, mem m')])
`;

(* Old experimental stuff:
val compute_next_store_def = Define `compute_next_store (core cid p s) (mem m) =
  case next_stmt s of
      NONE => []
    | SOME (t0, BStmtB (BStmt_Assign v ex)) =>
        if is_mem v
        then (let m' = m with <| bmst_inflight updated_by
			         (APPEND [(cid,BirInflight (memfresh m) (BStmtB (BStmt_Assign v ex)))]);
		                 bmst_counter updated_by (\n:num.n+1) |>;
	      in let s' = s with bst_inflight updated_by (remove_inflight t0)
              in [(core cid p s', mem m')])
        else []
`;
val compute_next_load_def = Define `compute_next_load (core cid p s) (mem m) =
  case next_stmt s of
      NONE => []
    | SOME (t0, BStmtB (BStmt_Assign v ex)) =>
	if exp_is_load ex
	then case bir_eval_exp ex m.bmst_environ of
	         NONE => []
	       | SOME value =>
	           case bir_env_write v value s.bst_environ of
		       NONE => []
		     | SOME env' =>
		         (let s' = s with <| bst_inflight updated_by (remove_inflight t0);
		                             bst_environ := env'  |>
		          in [(core cid p s', mem m)])
	else []
`;

val update_core_def = Define `
  (update_core cid c [] = [(cid,c)]) /\
  (update_core cid c ((x,y)::cores) =
     if cid = x
     then (x,c)::cores
     else (x,y)::update_core cid c cores)
`;

(* val _ = enable_monadsyntax(); *)
val compute_next_par_def = Define `
  compute_next_par (cores:(num # sys_st) list, m) =
     LIST_BIND cores (\ (cid,c).
	LIST_BIND (APPEND (compute_next_par_single c m)
			     (APPEND (compute_next_par_mem c m)
				     (APPEND (compute_next_load c m)
					     (compute_next_store c m))))
		  (\ (c',m') . [(update_core cid c' cores, m')]))
`;
                                       
val compute_next_par_steps_def = Define `
  compute_next_par_steps (n:num) (cores:(num # sys_st) list, m) =
    if n = 0
    then [(cores,m)]
    else LIST_BIND (compute_next_par (cores,m)) (\s2. compute_next_par_steps (n-1) s2)
`;
*)
val _ = export_theory ();
