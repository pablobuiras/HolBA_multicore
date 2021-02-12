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

(* TODO: Check all expressions for loads and stores better *)
val stmt_is_memop_def = Define `
  (stmt_is_memop (BStmtB BStmt_Fence) = T) /\
  (stmt_is_memop (BStmtB (BStmt_Assign var exp)) = ((is_mem var) \/ (exp_is_load exp))) /\
  (stmt_is_memop _ = F)
`;

val block_is_atomic_def = Define `block_is_atomic p s =
  case (bir_get_program_block_info_by_label p (s.bst_pc.bpc_label)) of
      NONE => F
    | SOME (i,blk) => blk.bb_atomic
`;

(* ------------------------------------------------------------------------- *)
(*  Nondeterministic step relation with pipelining                           *)
(* ------------------------------------------------------------------------- *)

(* Single core steps. *)
(* TODO: Forbid memory operations *)
val (bir_pstep_rules, bir_pstep_ind, bir_pstep_cases) = Hol_reln `
  (* Regular execution of statements without memory operations *)
  (* Note that this cannot be used inside atomic blocks *)
  (!p st st' oo stmt.
   ((bir_get_current_statement p st.bst_pc = SOME stmt) /\
    (bir_exec_stmt p stmt st = (oo, st')) /\
    (~(block_is_atomic p st)) ∧
    ~(stmt_is_memop stmt)
   ) ⇒
   pstep p st st'
  )
`;

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

(* TODO: Move these to programScript *)

val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_status_ss = rewrites (type_rws ``:bir_status_t``);

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

val lock_held_def = Define`
  (lock_held m cid =
    (m.bmst_lock = SOME cid))
`;

val lock_free_def = Define`
  (lock_free m =
    (m.bmst_lock = NONE))
`;


val (parstep_rules, parstep_ind, parstep_cases) = Hol_reln`
  (* Obtain a memory core lock for some core, when you have entered
   * (but not started executing) an atomic block.
   * This can only be done if no other core holds the lock,
   * and if store buffer does not contain any
   * operations associated with the current core. *)
  (!cid p st m m' system.
   (core cid p st) IN system /\
   (mem m) IN system /\
   block_is_atomic p st /\
   m.bmst_lock = NONE /\
   buffer_is_empty m cid /\
   m' = m with <| bmst_lock := SOME cid |> ==>
   parstep system (system DIFF {mem m} UNION {mem m'})
  ) /\
  (* Take a regular, non-memory basic statement step while holding lock. *)
  (* NOTE: You are implicitly in an atomic block in this and the below rule. *)
  (!cid p st st' system bstmt.
   (core cid p st) IN system /\
   (mem m) IN system /\
   m.bmst_lock = SOME cid /\
   (bir_get_current_statement p st.bst_pc = SOME (BStmtB bstmt)) /\
   ~(stmt_is_memop (BStmtB bstmt)) ∧
   (bir_exec_stmt p (BStmtB bstmt) st = (oo, st')) ⇒
   parstep system (system DIFF {core cid p st} UNION {core cid p st'})
  ) /\
  (* Exiting a block with the lock releases the memory core lock. *)
  (!cid p st m m' system end_stmt.
   (core cid p st) IN system /\
   (mem m) IN system /\
   m.bmst_lock = SOME cid /\
   buffer_is_empty m cid /\
   (bir_get_current_statement p st.bst_pc = SOME (BStmtE end_stmt)) /\
   (bir_exec_stmt p (BStmtE end_stmt) st = (oo, st')) /\
   m' = m with <| bmst_lock := NONE |> ==>
   parstep system ((system DIFF {mem m} UNION {mem m'})
                   DIFF {core cid p st} UNION {core cid p st'})
  ) /\
  (* Perform an execution step for a single core. *)
  (!cid p st st' system.
   pstep p st st' /\
   (core cid p st) IN system ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'})
  ) /\
  (* Perform a step for a memory - note that with the
   * current definition of memstep this is identical with committing
   * something from the write buffer. *)
  (!m m' system.
   memstep m m' /\
   (mem m) IN system ==>
   parstep system (system DIFF {mem m} UNION {mem m'})
  ) /\
  (* Perform a fence step for a single core and a single memory.
   * This can only be done if write buffer does
   * not contain any statement associated with the current core.. *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m m' system system'.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    (* This would force the core to flush its in-flight set
    /\ s' = pstep_flush p s *)
    (* This would force a memory to flush its in-flight set
    /\ m' = memflush cid m.bmst_inflight m *)
    (* This forces a memory to have an empty in-flight set *)
    buffer_is_empty m cid /\
    (bir_get_current_statement p st.bst_pc = SOME (BStmtB BStmt_Fence)) /\
    (bir_exec_stmt p (BStmtB BStmt_Fence) st = (oo, st')) /\
    system' = (system DIFF {core cid p st} UNION {core cid p st'})
		DIFF {mem m} UNION {mem m'}) ==>
   parstep system system'
  ) /\
  (* Store to memory (in-flight set)
   * This can only be done if lock is not held by some other core. *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m m' system var mem_ex addr_ex en val_ex addr value.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    ((lock_held m cid) ∨ (~(block_is_atomic p st) ∧ lock_free m)) /\
    (* TODO: Implicit assumption that mem_ex is main memory *)
    (bir_get_current_statement p st.bst_pc = SOME (BStmtB (BStmt_Assign var (BExp_Store mem_ex addr_ex en val_ex)))) /\
    (?t. var = BVar "MEM" t) /\
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (SOME value = bir_eval_exp val_ex st.bst_environ) /\
    (* TODO: This must not put statements to in-flight set, but rather "writes" where
     * the expressions have been evaluted. *)
    (m' = m with <|bmst_buffer updated_by
		     (APPEND [(cid, BEv_Write (memfresh m) var addr en value)]);
		     bmst_counter updated_by (\n:num. n+1)|>) /\
    (st' = st with bst_pc updated_by bir_pc_next)) ==>
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
  (!cid p st st' m system var mem_var addr_ex en it addr mem_val value env'.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    ((lock_held m cid) ∨ (~(block_is_atomic p st) ∧ lock_free m)) /\
    (bir_get_current_statement p st.bst_pc = SOME (BStmtB (BStmt_Assign var (BExp_Load (BExp_Den mem_var) addr_ex en it)))) /\
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (buffer_bypass_read m cid addr = NONE) /\
    (* TODO: Implicitly assumed that ex1 actually evaluates to "MEM" *)
    (SOME mem_val = bir_eval_exp (BExp_Den mem_var) m.bmst_environ) /\
    (SOME value = bir_eval_load (SOME mem_val) (SOME addr) en it) /\
    (SOME env' = bir_env_write var value st.bst_environ) /\
    (st' = st with <|bst_environ := env'; bst_pc := (bir_pc_next st.bst_pc)|>)) ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'})) /\
  (* Load from write buffer *)
  (* TODO: Note that this is done in relation to an arbitrary memory.
   *       In its current formulation, this is nonsensical for
   *       systems with multiple memories. *)
  (!cid p st st' m system var mem_ex addr_ex en it addr wcid wid mem_var value env'.
   ((core cid p st) IN system /\
    (mem m) IN system /\
    ((lock_held m cid) ∨ (~(block_is_atomic p st) ∧ lock_free m)) /\
    (bir_get_current_statement p st.bst_pc = SOME (BStmtB (BStmt_Assign var (BExp_Load mem_ex addr_ex en it)))) /\
    (* TODO: Currently, we don't care about the value of mem_ex, since we only deal
     * with one main memory. *)
    (SOME addr = bir_eval_exp addr_ex st.bst_environ) /\
    (* TODO: Endianness currently ignored, but must be matched... *)
    (buffer_bypass_read m cid addr = SOME (wcid, BEv_Write wid mem_var addr en value)) /\
    (SOME env' = bir_env_write var value st.bst_environ) /\
    (st' = st with <|bst_environ := env'; bst_pc := (bir_pc_next st.bst_pc)|>)) ==>
   parstep system (system DIFF {core cid p st} UNION {core cid p st'}))
`;

val par_traces_def = Define `par_traces system =
  gen_traces parstep
`;

val compute_next_par_single_def = Define `compute_next_par_single (core cid p s) m =
  LIST_BIND ([bir_exec_step_state p s]) (\s'. [(core cid p s', m)])
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
