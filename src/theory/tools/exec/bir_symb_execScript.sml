(* Vim users execute the following loads *)
(*
app load ["HolKernel", "Parse", "boolLib" ,"bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_valuesTheory"];
app load ["bir_symb_envTheory"];
app load ["bir_programTheory", "bir_expTheory", "bir_envTheory"];
app load ["llistTheory", "wordsLib"];
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_envTheory;
open bir_expTheory;
open bir_programTheory;
open llistTheory wordsLib;

open bir_envTheory bir_symb_envTheory;

val _ = new_theory "bir_symb_exec";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)


(* *
 * Symbolic State contains of:
 * PC: current program counter 
 * environment: Mapping vars to expressions 
 * memory: Mapping memory addresses to expressions
 * pred: expression representing the path condition
 * bsst_status : a status bit (mainly used for errors) 
 * *)

val _ = Datatype `bir_symb_state_t = <|
  bsst_pc           : bir_programcounter_t; 
  bsst_environ      : bir_symb_var_environment_t; (* Mapping Vars to Exps *)
  bsst_pred         : bir_exp_t; (* Path predicate *)
  bsst_status       : bir_status_t;
 |>`;

(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)

(* Initially, Environment is empty and predicate set to True *)
val bir_symb_state_init_def = Define `bir_symb_state_init (p : 'a bir_program_t) env pred = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := env;
    bsst_pred       := pred;
    bsst_status     := BST_Running |>`;

val bir_symb_state_set_failed_def = Define `
    bir_symb_state_set_failed st = 
      (st with bsst_status := BST_Failed)`;

val bir_symb_state_set_typeerror_def = Define `
    bir_symb_state_set_typeerror st = 
    st with bsst_status := BST_TypeError`;

val bir_symb_state_is_terminated_def = Define `
    bir_symb_state_is_terminated st = 
      (st.bsst_status <> BST_Running)`;



val bir_symb_state_cstr_def = Define `
    bir_symb_state_cstr bst pred =
      <|
	bsst_pc      := bst.bst_pc;
	bsst_environ := bir_symb_env_cstr bst.bst_environ;
	bsst_pred    := pred;
	bsst_status  := bst.bst_status;
       |>
    `;

val bir_symb_state_dstr_def = Define `
    bir_symb_state_dstr bsst =
      <|
	bst_pc       := bsst.bsst_pc;
	bst_environ  := bir_symb_env_dstr bsst.bsst_environ;
	bst_status   := bsst.bsst_status;
       |>
    `;

(* ------------------------------------------------------------------------- *)
(* Eval certain expressions                                                  *)
(* Different from concrete Execution, this returns a BIR Expression          *)        
(* ------------------------------------------------------------------------- *)

val bir_symb_esubst_cast_def =  Define `
    bir_symb_esubst_cast ct eo ty =
      case eo of
       | NONE => NONE
       | SOME e => SOME (BExp_Cast ct e ty)`;

val bir_symb_esubst_unary_def = Define `
    bir_symb_esubst_unary et eo =
      case eo of
       | NONE => NONE
       | SOME e => SOME (BExp_UnaryExp et e)`;

val bir_symb_esubst_binary_def = Define `
    bir_symb_esubst_binary et eo1 eo2 =
      case (eo1, eo2) of
       | (NONE, _) => NONE
       | (_, NONE) => NONE
       | (SOME e1, SOME e2) => SOME (BExp_BinExp et e1 e2)`;

val bir_symb_esubst_bin_pred_def = Define `
    bir_symb_esubst_bin_pred pt eo1 eo2 =
      case (eo1, eo2) of
       | (NONE, _) => NONE
       | (_, NONE) => NONE
       | (SOME e1, SOME e2) => SOME (BExp_BinPred pt e1 e2)`;

val bir_symb_esubst_memeq_def = Define `
    bir_symb_esubst_memeq eo1 eo2 =
      case (eo1, eo2) of
       | (NONE, _) => NONE
       | (_, NONE) => NONE
       | (SOME e1, SOME e2) => SOME (BExp_MemEq e1 e2)`;

val bir_symb_esubst_ite_def = Define `
    bir_symb_esubst_ite co eot eof =
      case (co, eot, eof) of
       | (NONE, _, _) => NONE
       | (_, NONE, _) => NONE
       | (_, _, NONE) => NONE
       | (SOME c, SOME et, SOME ef) => SOME (BExp_IfThenElse c et ef)`;

val bir_symb_esubst_load_def = Define `
    bir_symb_esubst_load mem_eo a_eo en ty =
      case (mem_eo, a_eo) of
       | (NONE, _) => NONE
       | (_, NONE) => NONE
       | (SOME mem_e, SOME a_e) => SOME (BExp_Load mem_e a_e en ty)`;

val bir_symb_esubst_store_def = Define `
    bir_symb_esubst_store mem_eo a_eo en v_eo =
      case (mem_eo, a_eo, v_eo) of
       | (NONE, _, _) => NONE
       | (_, NONE, _) => NONE
       | (_, _, NONE) => NONE
       | (SOME mem_e, SOME a_e, SOME v_e) => SOME (BExp_Store mem_e a_e en v_e)`;


(* this is like a substitution using a symbolic environment and this is
   SOME expression if the resulting expression does not contain any
   BExp_Den nodes anymore, otherwise NONE *)
val bir_symb_esubst_exp_def = Define `
   (bir_symb_esubst_exp (BExp_Const n) env = SOME (BExp_Const n)) /\

   (bir_symb_esubst_exp (BExp_Den v) env = bir_symb_env_read v env) /\

   (bir_symb_esubst_exp (BExp_Cast ct e ty) env = 
	      bir_symb_esubst_cast ct
                (bir_symb_esubst_exp e env) ty) /\

   (bir_symb_esubst_exp (BExp_UnaryExp et e) env =
	      bir_symb_esubst_unary et
                (bir_symb_esubst_exp e env)) /\

   (bir_symb_esubst_exp (BExp_BinExp et e1 e2) env = 
	      bir_symb_esubst_binary et 
		(bir_symb_esubst_exp e1 env)
		(bir_symb_esubst_exp e2 env)) /\

   (bir_symb_esubst_exp (BExp_BinPred pt e1 e2) env = 
	      bir_symb_esubst_bin_pred pt
		(bir_symb_esubst_exp e1 env)
		(bir_symb_esubst_exp e2 env)) /\

   (bir_symb_esubst_exp (BExp_MemEq e1 e2) env = 
	      bir_symb_esubst_memeq
		(bir_symb_esubst_exp e1 env)
		(bir_symb_esubst_exp e2 env)) /\

   (bir_symb_esubst_exp (BExp_IfThenElse c et ef) env = 
	      bir_symb_esubst_ite
		(bir_symb_esubst_exp c env) 
		(bir_symb_esubst_exp et env)
		(bir_symb_esubst_exp ef env)) /\

   (bir_symb_esubst_exp (BExp_Load mem_e a_e en ty) env =
	      bir_symb_esubst_load
		(bir_symb_esubst_exp mem_e env) 
		(bir_symb_esubst_exp a_e env)
		en
		ty) /\

   (bir_symb_esubst_exp (BExp_Store mem_e a_e en v_e) env = 
	      bir_symb_esubst_store
		(bir_symb_esubst_exp mem_e env)
		(bir_symb_esubst_exp a_e env)
		en
		(bir_symb_esubst_exp v_e env))`;


val bir_symb_eval_exp_def = Define `
    bir_symb_eval_exp e env =
      case bir_symb_esubst_exp e env of
        | SOME ex => bir_eval_exp ex (BEnv (K NONE))
	| NONE    => NONE (* if some variables are not in env *)
    `;


(* ------------------------------------------------------------------------- *)
(* Symbolic Execution Semantics                                              *)
(* ------------------------------------------------------------------------- *)

(*
   NOTE: at this point we assume the expressions to be evaluatable to constants
     - a possible preprocessing to ensure this:
       - use an SMT solver to find all possible outcomes, and
       - transform the program accordingly
*)
val bir_symb_eval_label_exp_def = Define `
   (bir_symb_eval_label_exp (BLE_Label l) env = SOME l) ∧
   (bir_symb_eval_label_exp (BLE_Exp e) env =
      case bir_symb_eval_exp e env of
        | BVal_Imm i => SOME (BL_Address i)
        | _ => NONE
   )`;


(********************)
(* Jumps/Halt       *)
(********************)

(* jump to a label *)
val bir_symb_exec_stmt_jmp_to_label_def = Define `
    bir_symb_exec_stmt_jmp_to_label
      (p: 'a bir_program_t) (l: bir_label_t) (st: bir_symb_state_t) = 
    if (MEM l (bir_labels_of_program p)) then 
      st with bsst_pc := bir_block_pc l
    else (st with bsst_status := (BST_JumpOutside l))`;
    

(* unconditional jump *)
val bir_symb_exec_stmt_jmp_def = Define `
    bir_symb_exec_stmt_jmp 
      (p: 'a bir_program_t) (le: bir_label_exp_t) (st: bir_symb_state_t) = 
    case bir_symb_eval_label_exp le st.bsst_environ of 
    | NONE   => bir_symb_state_set_failed st 
    | SOME l => bir_symb_exec_stmt_jmp_to_label p l st`;

(* halt *)
val bir_symb_exec_stmt_halt_def = Define `
    bir_symb_exec_stmt_halt ex (st: bir_symb_state_t) = 
      case bir_symb_eval_exp ex st.bsst_environ of
	| NONE => bir_symb_state_set_typeerror st
	| SOME v => st with bsst_status := BST_Halted v
    `;

(* conditional jump, "forks" in symbolic execution:
 * is a list containing two states with 
 * updated path predicate accordingly *)
val bir_symb_exec_stmt_cjmp_def = Define `
    bir_symb_exec_stmt_cjmp (p: 'a bir_program_t) ex l1 l2 st =
(* whenever we would normally evaluate an expression,
     we have to apply environment based substitution *)
(* this means specifically: whenever we append to the path predicate,
     we have to apply substitution of variables based on the current symbolic environment *)
    case bir_symb_esubst_exp ex st.bsst_environ of
      | NONE => [bir_symb_state_set_failed st]
      | SOME ex_subst => (
	  let
	    st_true  = bir_symb_exec_stmt_jmp p l1 st;
	    st_false = bir_symb_exec_stmt_jmp p l2 st;
	  in
	  [
	    st_true  with bsst_pred :=
	      (BExp_BinExp BIExp_And ex_subst st.bsst_pred)
	   ;
	    st_false with bsst_pred :=
	      (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex_subst) st.bsst_pred)
	  ]
        )`;

(* execute "end" (jumps/halt) statement *)
val bir_symb_exec_stmtE_def = Define `
   (bir_symb_exec_stmtE (p: 'a bir_program_t) (BStmt_Jmp l) st =
      [bir_symb_exec_stmt_jmp p l st])
   /\
   (bir_symb_exec_stmtE p (BStmt_CJmp ex l1 l2 ) st =
       bir_symb_exec_stmt_cjmp p ex l1 l2 st)
   /\
   (bir_symb_exec_stmtE p (BStmt_Halt ex) st =
      [bir_symb_exec_stmt_halt ex st])
   `;


(********************)
(* basic statements *)
(********************)
val bir_symb_exec_stmt_assign_def = Define `
    bir_symb_exec_stmt_assign v ex (st: bir_symb_state_t) =
      let
        env_o = case bir_symb_esubst_exp ex st.bsst_environ of
                  | SOME ex_subst => bir_symb_env_write v ex_subst st.bsst_environ
                  | NONE => NONE;
      in
      case env_o of 
        | SOME env => st with bsst_environ := env
        | NONE     => bir_symb_state_set_typeerror st`;

(* assert and assume *)
val bir_symb_exec_stmt_assert_def = Define `
    bir_symb_exec_stmt_assert ex st =
    case bir_symb_esubst_exp ex st.bsst_environ of
      | NONE => [(NONE, bir_symb_state_set_failed st)]
      | SOME ex_subst => (
	  let
	    st_true  = st;
	    st_false = (st with bsst_status := BST_AssertionViolated);
	  in
	  [
	    (NONE, st_true  with bsst_pred :=
	      (BExp_BinExp BIExp_And ex_subst st.bsst_pred))
	   ;
	    (NONE, st_false with bsst_pred :=
	      (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex_subst) st.bsst_pred))
	  ]
        )`;
val bir_symb_exec_stmt_assume_def = Define `
    bir_symb_exec_stmt_assume ex st =
    case bir_symb_esubst_exp ex st.bsst_environ of
      | NONE => [(NONE, bir_symb_state_set_failed st)]
      | SOME ex_subst => (
	  let
	    st_true  = st;
	    st_false = (st with bsst_status := BST_AssumptionViolated);
	  in
	  [
	    (NONE, st_true  with bsst_pred :=
	      (BExp_BinExp BIExp_And ex_subst st.bsst_pred))
	   ;
	    (NONE, st_false with bsst_pred :=
	      (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex_subst) st.bsst_pred))
	  ]
        )`;


val bir_symb_exec_stmt_observe_def = Define `
    bir_symb_exec_stmt_observe ec el (obf:bir_val_t list -> 'a) st =
    case bir_symb_esubst_exp ec st.bsst_environ of
      | NONE => [(NONE, bir_symb_state_set_failed st)]
      | SOME ex_subst => (
	  [
	    (SOME (obf, (MAP (\e. bir_symb_esubst_exp e st.bsst_environ) el)),
              st with bsst_pred :=
	        (BExp_BinExp BIExp_And ex_subst st.bsst_pred))
	   ;
	    (NONE,
              st with bsst_pred :=
	        (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex_subst) st.bsst_pred))
	  ]
        )`;


(* execution of a basic statement *)
val bir_symb_exec_stmtB_def = Define `
   (bir_symb_exec_stmtB (BStmt_Assert ex) st
       =  bir_symb_exec_stmt_assert ex st)
   /\
   (bir_symb_exec_stmtB (BStmt_Assume ex) st
       =  bir_symb_exec_stmt_assume ex st)
   /\
   (bir_symb_exec_stmtB (BStmt_Assign v ex) st
       = [(NONE, bir_symb_exec_stmt_assign v ex st)])
   /\
   (bir_symb_exec_stmtB (BStmt_Observe ec el (obf:bir_val_t list -> 'a)) st
       = bir_symb_exec_stmt_observe ec el obf st)`;

(* execution of one statement *)
val bir_symb_exec_stmt_def = Define `
   (bir_symb_exec_stmt (p: 'a bir_program_t)
                       (BStmtB (bst: 'a bir_stmt_basic_t))
                       (st: bir_symb_state_t) =
        MAP
        (\(oo, st').
	  if (bir_symb_state_is_terminated st') then
	    (oo, st')
	  else
	    (oo, st' with bsst_pc updated_by bir_pc_next)
        )
        (bir_symb_exec_stmtB bst st))
   /\
   (bir_symb_exec_stmt p
                       (BStmtE (bst: bir_stmt_end_t))
                       st =
        MAP
        (\st'. (NONE, st'))
        (bir_symb_exec_stmtE p bst st))
   `;

(* execute one step *)
val bir_symb_exec_step_def = Define `
    bir_symb_exec_step (p: 'a bir_program_t) state =
      if (bir_symb_state_is_terminated state) then [(NONE, state)] else
      case (bir_get_current_statement p state.bsst_pc) of
	| NONE     => [(NONE, bir_symb_state_set_failed state)]
	| SOME stm => (bir_symb_exec_stmt p stm state)
    `;


(* ------------------------------------------------------- *)
(* connection between bir_symb_exec_step and bir_exec_step *)
(* ------------------------------------------------------- *)

(* connecting the states after one step *)
val bir_symb_exec_step_THM = prove(``
  (bsst = bir_symb_state_cstr bst pred) ==>

  ((oo,bst') = bir_exec_step p bst) ==>
  (MEM (soo,bsst') (bir_symb_exec_step p bsst)) ==>

  (bir_eval_exp (bsst'.bsst_pred) (bst.bst_environ) = bir_val_true) ==>

  (bir_symb_state_dstr bsst' = bst')
``,
cheat
);



(*
(* ----------------------------------------------------- *)
(* definitions for evaluating the execution of a program *)
(* ----------------------------------------------------- *)

(* Execute a Basic Block *)
val bir_symb_exec_stmtB_list_def = Define `
   (bir_symb_exec_stmtB_list (p: 'a bir_program_t) (st: bir_symb_state_t) [] =
      st)
   /\
   (bir_symb_exec_stmtB_list p st ((stmt:'a bir_stmt_basic_t) :: stmt_list) = 
      bir_symb_exec_stmtB_list p (bir_symb_exec_stmtB stmt st) stmt_list)
   `;


val bir_symb_exec_blk_def = Define `
    (bir_symb_exec_blk 
        (p: 'a bir_program_t) (blk: 'a bir_block_t) (st: bir_symb_state_t ) = 
        bir_symb_exec_stmtE p (blk.bb_last_statement) 
            (bir_symb_exec_stmtB_list p st (blk.bb_statements))
    )`;
        
val bir_symb_exec_first_blk_def = Define `
    (bir_symb_exec_first_blk 
        (BirProgram (blk_list : ('a bir_block_t) list)) (st: bir_symb_state_t) = 
        bir_symb_exec_blk (BirProgram blk_list) (HD blk_list) st)`;

(* Execute each BB in a program *)

val bir_symb_exec_label_block_def = Define `
    bir_symb_exec_label_block (p: 'a bir_program_t) (st: bir_symb_state_t) = 
    case (bir_get_program_block_info_by_label p st.bsst_pc.bpc_label) of 
    | NONE => ([], [bir_symb_state_set_failed st])
    | SOME (_, blk) => if bir_symb_state_is_terminated st
                       then ([], [st]) else (bir_symb_exec_blk p blk [st])`;
*)

    
val _ = export_theory();
