open wordsTheory
open bir_promisingTheory;

open bslSyntax pairSyntax numSyntax listSyntax
open bir_programSyntax

open computeLib
open herdLitmusValuesLib
open litmusInterfaceLib
	 
open wordsLib stringLib;


val _ = add_thms (CONJUNCTS LITMUS_CONSTANT_THM) the_compset;
val _ = add_words_compset true the_compset;

val term_EVAL = rhs o concl o EVAL

(* Make cores *)
 fun mk_cores programs environs =
    let
	fun loop n [] = []
	  | loop n ((p,e)::l) = 
	    let val cid = term_of_int n;
		val s = “bir_state_init ^p with <| bst_environ := BEnv ^e |>”;
		val core = term_EVAL “Core ^cid ^p ^s”
	    in core::loop (n+1) l end;
	val cores = loop 0 (zip programs environs)
    in mk_list (cores, “:core_t”) end;

(* Promise mode execution *)
fun promiseRun fuel coresAndMemory =
    let
	val newCoresAndMemory = term_EVAL “eval_pmstepO1 ^fuel ^coresAndMemory”;
	val (l, ty) = dest_list newCoresAndMemory;
    in
	if null l then (* No more promises *)
	    [coresAndMemory]
	else
	    List.concat (List.map (promiseRun fuel) l)
    end;

local
    fun nonPromiseRunAux fuel memory core =
	let val term = “FILTER is_final_core $ eval_clsteps_coreO1 ^fuel ^core ^memory”
	in fst (dest_list(term_EVAL term)) end;

    (* Cartesian product *)
    fun cartProd [] = []
      | cartProd [h] = map (fn e => [e]) h
      | cartProd (h::l) = 
	let val l' = cartProd l in 
	    List.concat $ map (fn x => map (fn y => y::x) h) l'
        end;
in
(* Non-promise mode execution *)
fun nonPromiseRun fuel coresAndMemory =
    let
	val (cores, memory) = dest_pair coresAndMemory;
	val (cores', core_ty) = dest_list cores;
	val coress = map (nonPromiseRunAux fuel memory) cores';
	val coress' = map (fn cs => mk_list(cs,core_ty)) (cartProd coress)
    in map (fn cs => mk_pair(cs,memory)) coress' end;
end

fun getRegistersAndMemory coresAndMemory =
    let
	val (cores, memory) = dest_pair coresAndMemory
	val regs = “MAP (\t. case t of (Core cid p s) => case s.bst_environ of BEnv f => f) ^cores”
	val memory' = “FOLDL (\t m. t (|m.loc |-> SOME m.val|)) (K NONE) ^memory”;
    in term_EVAL $ mk_pair (memory', regs) end;

(* 
fun getStatesAndMemory coresAndMemory = 
    let
        val (cores, memory) = dest_pair
	val states = “MAP (\t. case t of (Core cid p s) => s) ^cores”
     in (states, memory)

val filename = "./tests/BASIC_2_THREAD/LB+fence.rw.rws.litmus";
val filename = "./tests/ATOMICS/CO/2+2W+fence.rw.rws+pospx.litmus";
val testRecord = lift_herd_litmus filename;
val fuel = 64;
*)

fun run_litmus fuel filename =
   let 
       (* Load litmus test *)
       val testRecord  = load_litmus filename;
       (* Fuel used for promise and non-promise execution *)
       val fuelTerm = term_of_int fuel;
       (* Set default state *)
       val cores = mk_cores (#progs testRecord) (#inits testRecord);
       val coresAndEmptyMemory = mk_pair(cores,mk_list([],“:mem_msg_t”));
       (* Make promise only run *)
       val coresAndPromises = promiseRun fuelTerm coresAndEmptyMemory;
       (* Make non-promising runs *)
       val coresAndPromisesFinal = List.concat (map (nonPromiseRun fuelTerm) coresAndPromises);
       (* Get the final states of registers and memory *)
       val finalStates = map getRegistersAndMemory coresAndPromisesFinal
       val finalStatesTerm = mk_list(finalStates, 
				     “:(bir_val_t -> bir_val_t option) # ((string -> bir_val_t option) list)”);
       (* Get the post-condition *)
       val finalPredicate = #final testRecord;
       (* Testing of post-condition *)
       val finalTest = term_EVAL “^(#final testRecord) ^finalStatesTerm”
    in 
	if null coresAndPromises orelse null coresAndPromisesFinal then
	    (* If we have no states, exit *)
	    "ExecError"
	else
	    fromHOLstring $ term_EVAL “if ^finalTest then "Ok" else "No"”
    end;

fun main () =
    let
	val arguments = CommandLine.arguments ();
	val inputfile = List.last arguments;
	val result    = run_litmus 64 inputfile
    in print $ inputfile ^ " " ^ result ^ "\n" end;

