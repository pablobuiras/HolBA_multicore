
open HolKernel Parse boolLib bossLib;

open bslSyntax;

open numSyntax pairSyntax listSyntax;
open bir_multicoreSyntax bir_programSyntax;

val _ = new_theory "peterson";

fun bloadvar var n =
    bload64_le (bden (bvarmem64_8 "MEM"))
               (bplus (bden (bvarimm64 var),
                       bconst8 n));

fun bstorevar var n v =
    bassign (bvarmem64_8 "MEM",
             bstore_le (bden (bvarmem64_8 "MEM"))
                       (bplus (bden (bvarimm64 var),
                               bconst8 n)) v);

exception WrongCore;
fun other_core n =
    case n of
        0 => 1
      | 1 => 0
      | _ => raise WrongCore;

fun critical_section core =
    bassign (bvarmem64_8 "MEM",
             bstore_le (bden (bvarmem64_8 "MEM"))
                       (bden (bvarimm64 "shared")) (bconst8 1));

fun petersons core =
    bdefprog_list (Type`:'a`) ("p_"^PolyML.makestring core)
                  [(blabel_str ("P"^PolyML.makestring core),

                 [bstorevar "flag" core btrue
                 ,bstorevar "turn" 0 (bconst1 (other_core core))
                 ],

                 (bjmp o belabel_str) "loop")

                  ,(blabel_str "loop",
                    [bassign (bvarimm8 "f", bloadvar "flag" (other_core core))
                    ,bassign (bvarimm8 "t", bloadvar "turn" 0)
                    ,bassign (bvarimm 1 "cond",
                              band (beq
                                        (bden (bvarimm8 "f"),
                                         (bconst64 1))
                                   ,beq
                                        (bden (bvarimm8 "t"),
                                         bconst1 (other_core core))))
                    ],

                    bcjmp (bden (bvarimm1 "cond"),
                           belabel_str "loop",
                           belabel_str "critical"))

                  ,(blabel_str "critical",
                    [critical_section core],
                    (bjmp o belabel_str) "end")

                  ,(blabel_str "end",
                    [bstorevar "flag" core bfalse],
                    (bhalt o bconst32) 0)];

(**********************************************)
(* Generalize these functions and move out to *)
(* appropriate places                         *) 

fun mk_init_peterson_core n =
  let
    val prog_def =
      INST_TYPE [alpha |-> ``:string``] (petersons n)
    val prog_tm =
        ((snd o dest_eq o concl) prog_def)
    val init_st = mk_bir_state_init prog_tm
  in
    mk_core (term_of_int n, prog_tm, init_st)
  end
;

(* Makes an initial multicore state for n cores. *)
local
  fun mk_init_peterson_cores' 0 = []
    | mk_init_peterson_cores' n =
      ((mk_pair (term_of_int (n-1), mk_init_peterson_core (n-1)))::
       (mk_init_peterson_cores' (n-1))
      )
in
fun mk_init_peterson_cores n =
  mk_list(rev (mk_init_peterson_cores' n),``:num # sys_st``)
end;

(* Makes the complete argument of "compute_next_par" *)
fun mk_init_peterson_par_st n =
  let
    val cores = mk_init_peterson_cores n
    val shared_mem = mem_init_tm
  in
    mk_pair (cores, shared_mem)
  end
;

val peterson_init_par_st = mk_init_peterson_par_st 2;

(* TODO: Different programs (* Label of first block *)? *)
(* TODO: Problem: state below is bir_state, when it should be
 * sys_st (cores part from above)... *)
Theorem peterson_mutual_exclusion:
!stl. is_trace prog stl ==>
  !n. (pc1,pc2) = (EL n stl).bst_pc ==>
  (pc1,pc2) <> (blabel_str "critical", blabel_str "critical")
Proof.
cheat
QED




val _ = export_theory();
