open litmusInterfaceLib;

fun typed_prog p = inst [alpha |-> Type`:string`] p;
fun fix_types ps = map typed_prog ps;

fun pp_litmus filename =
    let
      val test = load_litmus filename;
      val (progs as [prog1,prog2]) = fix_types (#progs test);
      val (mem,envs) = #inits test;
    in
      (List.app print_term progs; List.app print_term envs; print_term (#final test))
    end

fun litmus_filenames root =
    let open OS.FileSys;
        fun unfold_dirstream ds =
            case readDir ds of
                NONE => []
              | SOME elem => elem :: unfold_dirstream ds
        fun strcat s1 s2 = s1 ^ s2;
(*        fun process_subdir s =
            List.map (strcat (root ^ "/" ^ s ^ "/"))
            (unfold_dirstream (openDir (root^"/"^s))) *)
        fun expand path =
            if isDir path
            then let val tests_dirstream = openDir path;
                     val children =
                         List.map (strcat (path ^ "/")) (unfold_dirstream tests_dirstream);
                 in
                   flatten (List.map expand children)
                 end
            else [path];
    in
      expand root
    end;

fun find_litmus root p =
    let val all_tests = litmus_filenames root;
    in
      List.filter (p o load_litmus) all_tests
    end;

fun find_cjmp () =
    let val root = "tests/non-mixed-size";
        fun any p [] = false
          | any p (x::xs) = p x orelse any p xs
        fun any_cjmp (test:litmus) =
            let open bir_programSyntax;
                val progs = fix_types (#progs test);
                fun block_has_cjmp b =
                    let val (_,_,_,last_stmt) = dest_bir_block b
                    in
                      if is_BStmt_CJmp last_stmt
                      then (print_term b; true)
                      else false
                    end;
                fun has_cjmp prog =
                    let val (_,bs) = dest_BirProgram_list prog
                    in
                      any block_has_cjmp bs
                    end;
            in
              any has_cjmp progs
            end;
    in
      find_litmus root any_cjmp
    end

fun show_tests () =
    List.app pp_litmus
             ["tests/non-mixed-size/SAFE/RWC+addr+fence.rw.rw.litmus.json"
             ,"tests/non-mixed-size/SAFE/2+2W+fence.rw.rws.litmus.json"
             ]


(* cjmp tests:
computed with ‘find_cjmp ()’
*)
val cjmp_tests =
   ["tests/non-mixed-size/SAFE/ISA2+pos+ctrl+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+fence.rw.w.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-ws]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/SB+[rf-ctrlfencei-rf]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-ws]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-fr]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-fr]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/MP+fence.w.w+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/2+2W+[rf-ctrlfencei-fr]+fence.rw.w.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.rw.w+[fr-rf]-ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/MP+fence.rw.rw+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+fence.rw.w.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-fr]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.rw.rw+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.w.w+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrlfencei+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/R+[rf-ctrlfencei-fr]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrl+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrlfencei+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/Z6.0+pos+ctrl+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+poprl.litmus.json",
    "tests/non-mixed-size/SAFE/SB+[rf-ctrl-rf]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrl+addr.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrlfencei+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrl-ws]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrl-ws]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.w.w+[fr-rf]-ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/2+2W+[rf-ctrlfencei-fr]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-fr]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+poprl.litmus.json",
    "tests/non-mixed-size/SAFE/2+2W+[rf-ctrlfencei-fr]+fence.w.w.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrlfencei+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrl+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-fr]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+data.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrl+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-ws]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.rw.rw+[fr-rf]-ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+poprl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/ISA2+pos+ctrlfencei+addr.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrl-ws]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/W+RWC+pos+ctrlfencei+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/Z6.0+pos+ctrlfencei+fence.rw.rw.litmus.json",
    "tests/non-mixed-size/SAFE/2+2W+[rf-ctrlfencei-fr]+poprl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+fence.rw.w.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-ws]+poaqp.litmus.json",
    "tests/non-mixed-size/SAFE/S+fence.rw.w+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-fr]+data.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrl-ws]+ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/MP+fence.rw.w+[fr-rf]-ctrlfencei.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrlfencei-ws]+ctrl.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+addr.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrlfencei-ws]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/MP+[rf-ctrl-ws]+fence.r.rw.litmus.json",
    "tests/non-mixed-size/SAFE/S+[rf-ctrl-ws]+data.litmus.json",
    "tests/non-mixed-size/HAND/Andy27.litmus.json",
    "tests/non-mixed-size/HAND/ISA-DEP-WW-CTRL.litmus.json",
    "tests/non-mixed-size/HAND/ForwardAMO.litmus.json",
    "tests/non-mixed-size/HAND/ForwardSc.litmus.json"]
