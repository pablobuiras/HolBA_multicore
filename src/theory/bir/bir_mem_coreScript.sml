open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_programTheory;

val _ = new_theory "bir_mem_core";

(* ------------------------------------------------------------------------- *)
(*  Memory                                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_write_t =
  (* A write contains a unique string, the memory to be written to
   * (as a variable),
   * the address to be written to as well as the endianness to use,
   * and the value to be written. *)
    BEv_Write string bir_var_t bir_val_t bir_endian_t bir_val_t
`;

val mem_state_def = Datatype`
  mem_state_t = <|
    bmst_environ  : bir_var_environment_t;
    (*  bmst_status   : bir_status_t; *)
    bmst_lock     : num option;
    bmst_counter  : num;
    (* First argument is the core ID associated with the
     * write event *)
    (* TODO: This is currently a write buffer, but can later be generalised. *)
    bmst_buffer : (num # bir_write_t) list
    |>
`;

val memfresh_def = Define`
  memfresh st = STRCAT "mt" (n2s st.bmst_counter)
`;

val next_memop_def = Define`
  next_memop st =
    case st.bmst_buffer of
        [] => NONE
      | ((cid, BEv_Write evid mem_var addr en value)::t) =>
          SOME (evid, BEv_Write evid mem_var addr en value)
`;

(* This commits a memory operation from the list of events to memory *)
val commit_memop_def = Define`
  commit_memop (BEv_Write _ mem_var addr en value) st =
    case bir_eval_exp (BExp_Den mem_var) st.bmst_environ of
      | SOME mem =>
        case (bir_eval_store (SOME mem) (SOME addr) en (SOME value)) of
          | SOME mem' =>
	    (case bir_env_write mem_var mem' st.bmst_environ of
		 SOME env => (st with bmst_environ := env)
	       | NONE => ARB)
          | NONE => ARB
      | NONE => ARB
`;

val memflush_def = Define`
  (memflush target_cid [] st = st) /\
  (memflush target_cid ((cid, BEv_Write evid mem_var addr en value)::evts) st =
     if cid = target_cid
     then memflush target_cid evts (commit_memop (BEv_Write evid mem_var addr en value) st)
     else memflush target_cid evts st)
`;

val remove_mem_buffer_def = Define`
  remove_mem_buffer rem_evid l =
    FILTER (\evt. case evt of (_, BEv_Write evid _ _ _ _) => (rem_evid <> evid)) l
`;

val (memstep_rules, memstep_ind, memstep_cases) = Hol_reln`
  (!st st' evid evt.
   ((next_memop st = SOME (evid, evt)) /\
    (commit_memop evt st = st')
   ) ==>
   memstep st (st' with bmst_buffer updated_by (remove_mem_buffer evid)))
`;

val mem_compute_next_def = Define`
  mem_compute_next st =
    case next_memop st of
        NONE => []
      | SOME (evid, evt) =>
          [commit_memop evt st with bmst_buffer updated_by (remove_mem_buffer evid)]
`;

val mem_init_def = Define`
  mem_init =
    <| bmst_environ  := bir_env_default (bir_envty_of_vs {});
       bmst_counter  := 0;
       bmst_lock     := NONE;
       bmst_buffer := []
    |>
`;


val _ = export_theory ();

