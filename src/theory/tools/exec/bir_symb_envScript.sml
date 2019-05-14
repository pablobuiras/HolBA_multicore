(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_envTheory;
open bir_valuesTheory;
open listTheory;

(* --------------------------------------------------------------------- *)
(* Symbolic Environment:                                                 *)
(* Same as Concrete Environment, with initially all                      *)
(* variables / flags set to symbols                                      *)
(* ----------------------------------------------------------------------*)

val _ = new_theory "bir_symb_env";

val _ = Datatype `bir_symb_var_environment_t = 
  BSEnv (string |-> (bir_type_t # (bir_exp_t option)))`;
  

(* -----------------------------------------------------*)
(* Symbolic environment maps Vars to expressions        *)
(* ---------------------------------------------------- *)


val bir_symb_env_lookup_def = Define `
    bir_symb_env_lookup name (BSEnv env) = FLOOKUP env name`;

val bir_symb_env_update_def = Define `
    bir_symb_env_update varname eo ty (BSEnv env) = 
      if (?e. (eo = SOME e) /\ (SOME ty <> type_of_bir_exp e)) then
        NONE
      else
        SOME (BSEnv (FUPDATE env (varname, (ty, eo))))`;

val bir_symb_env_lookup_type_def = Define `
    bir_symb_env_lookup_type var_name env =
      OPTION_MAP FST (bir_symb_env_lookup var_name env)`;

val bir_symb_env_check_type_def = Define `
    bir_symb_env_check_type var env =
      (bir_symb_env_lookup_type (bir_var_name var) env = SOME (bir_var_type var))`;

val bir_symb_varname_is_bound_def = Define `
    bir_symb_varname_is_bound var_name (BSEnv env) = (var_name IN FDOM env)`;

val bir_symb_env_read_def = Define `
    bir_symb_env_read v env =
      case (bir_symb_env_lookup (bir_var_name v) env) of
       | NONE => NONE
       | SOME (_, NONE) => NONE
       | SOME (ty, SOME r) => if (ty = bir_var_type v) then SOME r else NONE`;

val bir_symb_env_write_def = Define `
    bir_symb_env_write v e env = 
      if bir_symb_env_check_type v env then 
        bir_symb_env_update (bir_var_name v) (SOME e) (bir_var_type v) env
      else
        NONE`;



val bir_valopt_to_const_def = Define `
    (bir_valopt_to_const (NONE) = NONE) /\
    (bir_valopt_to_const (SOME BVal_Unknown) = NONE) /\
    (bir_valopt_to_const (SOME (BVal_Imm n)) = SOME (BExp_Const n)) /\
    (bir_valopt_to_const (SOME (BVal_Mem aty vty mmap)) = SOME (BExp_MemConst aty vty mmap))
    `;

val bir_symb_env_cstr_def = Define `
    bir_symb_env_cstr (BEnv env) =
      BSEnv (FMAP_MAP2 (\(x,(ty,y)). (ty, bir_valopt_to_const y)) env)
    `;

val bir_symb_env_dstr_def = Define `
    bir_symb_env_dstr (BSEnv env) =
      BEnv (FMAP_MAP2 (\(x,(ty,y)). (ty, OPTION_MAP (\y. bir_eval_exp y (BEnv FEMPTY)) y)) env)
    `;



(*
TODO: define BEnv and BSEnv relation
TODO: proof properties, possibly with subst
 *)

val _ = export_theory ();
