open bir_promisingTheory
open wordsTheory

open bslSyntax pairSyntax numSyntax listSyntax
open bir_programSyntax

open computeLib
open herdLitmusValuesLib
open litmusInterfaceLib
	 
open wordsLib;


val _ = add_thms (CONJUNCTS LITMUS_CONSTANT_THM) the_compset;
val _ = add_words_compset true the_compset;

	 

val term_EVAL = rhs o concl o EVAL

(* Get thread registers *)
val get_TS = “\ts.
	      MAP (\t. case t of (Core cid p s) => 
				 case s.bst_environ of BEnv f => f) ts
	      ”;
(* Get writes to the memory *)
val get_M = “\m.
	     FOLDL (\t m. t (|m.loc |-> SOME m.val|)) (K NONE) m
	     ”;

(* Removes asserts *)
fun simplify_prog prog =
    let 
	val (block_list,ty) = dest_list (dest_BirProgram prog);
	fun fix_stmt stmt =
	    if is_BStmt_Assert stmt
	    then []
	    else  [stmt];
	fun fix_block block =
	    let val (lbl,is_atomic,stmts,last_stmt) = dest_bir_block block;
		val (stmt_list,stmt_ty) = dest_list stmts;
		val new_stmts = mk_list (List.concat (List.map fix_stmt stmt_list), stmt_ty);
	    in
		mk_bir_block (lbl,is_atomic,new_stmts,last_stmt)
	    end;
    in
	mk_BirProgram (mk_list (List.map fix_block block_list,ty))
    end;


fun mk_cores _ [] = []
  | mk_cores n ((p,e)::pes) = 
    let
	val cid = term_of_int n;
	val s = “bir_state_init ^p with <| bst_environ := BEnv ^e |>”;
    in
	“Core ^cid ^p ^s” :: mk_cores (n + 1) pes
    end;

fun run_litmus simplify filename =
   let 
       val test  = load_litmus filename;
       val progs = if simplify 
		   then (map simplify_prog (#progs test)) 
		   else (#progs test);
       val prog_envs = zip (#progs test) (#inits test);
       val cores = term_EVAL $ mk_list (mk_cores 0 prog_envs, “:core_t”);
       val final_states = term_EVAL “eval_promising 11 (^cores, [])”;
       val TS = term_EVAL “MAP (^get_TS o FST) ^final_states”
       val M = term_EVAL “MAP (^get_M o SND) ^final_states”
       val final = #final test
       val finals = term_EVAL “ZIP (^M, ^TS)”
       val res = term_EVAL “^final ^finals”
    in 
       case dest_list finals of
	    ([], ty) => "ExecError"
	  |  _ => (case term_to_string res of
		 "T" => "Ok"
	       | "F" => "No")
    end;

fun main () =
    let
	val arguments = CommandLine.arguments ();
	val inputfile = List.last arguments;
	val result    = run_litmus true inputfile
    in
	print $ inputfile ^ " " ^ result ^ "\n"
    end


(* 
fun find_tests () =
    let
	val proc = Unix.execute("/usr/bin/find", ["-iname", "*.json"])
	val inStream = Unix.textInstreamOf proc
    in
	String.tokens Char.isSpace (TextIO.inputAll inStream) before TextIO.closeIn inStream
    end


val filenames = find_tests ()
val basic = List.filter (String.isSubstring "X0") filenames
val simplify = true;
val filename = hd basic;
val res = run_litmus true (hd basic);
val pp = zip basic (map term_to_string res)
*)

