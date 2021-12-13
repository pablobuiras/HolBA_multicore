(* This is a slimmed-down version of BOOL_ss from bossLib *)

(*

HOL COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.

Copyright 1985--2021 by the HOL4 CONTRIBUTORS

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

  * The names of the copyright holders and contributors may not be
    used to endorse or promote products derived from this software
    without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
DAMAGE.

----------------------------------------------------------------------

Some files we distribute with HOL are the work of others, and we do
not and cannot claim copyright over them. Their copyrights may differ
from the above, but permit us to redistribute them. Such files
generally self-identify. In addition, we explicitly list the following
sub-directories as containing files governed by different copyright
notices.

See
  examples/muddy/LICENSE
  examples/muddy/muddyC/buddy/README
  examples/machine-code/graph/seL4-kernel/README
  src/HolSat/sat_solvers/minisat

- Files derived from SML/NJ are governed by the notice in
     doc/copyrights/smlnj.txt

- Some contributions have been explicitly put into the public domain
  by their authors: we cannot claim copyright on them individually. We
  have attempted to list these files in
     doc/copyrights/public-domain-contributions.txt.
----------------------------------------------------------------------

*)
structure bir_lifterSimps :> bir_lifterSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

local
  val x = mk_var ("x", Type.alpha)
  val y = mk_var ("y", Type.alpha)
  val P = mk_var ("P", bool)
  val Q = mk_var ("Q", bool)
  val R = mk_var ("R", bool)
  val xney = mk_neg (mk_eq (x, y))
  val idt' = GSYM IMP_DISJ_THM
  val th1 = REWR_CONV idt' (mk_disj (xney, P))
  val th2 = (REWR_CONV DISJ_COMM THENC REWR_CONV idt') (mk_disj (P, xney))
  val th3_c =
      LAND_CONV (REWR_CONV IMP_DISJ_THM) THENC REWR_CONV (GSYM DISJ_ASSOC) THENC
      REWR_CONV idt'
  val th3 = th3_c (mk_disj (mk_imp(P, Q), R))
in
  val lift_disj_eq = CONJ th1 th2
  val lift_imp_disj = CONJ th3 (ONCE_REWRITE_RULE [DISJ_COMM] th3)
end;

val BOOL_RED_ss = SSFRAG
  {name = SOME "BOOL",
   convs=[{name="BETA_CONV",
           trace=2,
           key=SOME ([],``(\x:'a. y:'b) z``),
           conv=K (K BETA_CONV)}],
   rewrs= map (fn s => (SOME{Thy = "bool",Name = s}, DB.fetch "bool" s)) [
     "REFL_CLAUSE", "EQ_CLAUSES", "NOT_CLAUSES",  "AND_CLAUSES",
     "OR_CLAUSES", "IMP_CLAUSES", "COND_CLAUSES", "FORALL_SIMP",
     "EXISTS_SIMP", "EXISTS_REFL", "EXISTS_UNIQUE_REFL",
     "EXCLUDED_MIDDLE", "bool_case_thm", "NOT_AND",
     "SELECT_REFL", "SELECT_REFL_2", "RES_FORALL_TRUE",
     "RES_EXISTS_FALSE"
   ] @ map (fn (s,th) => (SOME {Thy = "", Name = s}, th)) [
     ("EXISTS_REFL'", GSYM EXISTS_REFL),
     ("EXISTS_UNIQUE_REFL'", GSYM EXISTS_UNIQUE_REFL),
     ("EXCLUDED_MIDDLE'", ONCE_REWRITE_RULE [DISJ_COMM] EXCLUDED_MIDDLE),
     ("COND_BOOL_CLAUSES", COND_BOOL_CLAUSES),
     ("lift_disj_eq", lift_disj_eq),
     ("lift_imp_disj", lift_imp_disj)
   ],
   congs = [], filter = NONE, ac = [], dprocs = []};

val bool_multicore_ss = (pure_ss++BOOL_RED_ss++boolSimps.NOT_ss++boolSimps.CONG_ss++boolSimps.UNWIND_ss);

val std_multicore_ss = (pure_ss++numSimps.ARITH_RWTS_ss++combinSimps.COMBIN_ss++boolSimps.CONG_ss++boolSimps.NOT_ss++numSimps.REDUCE_ss++boolSimps.UNWIND_ss++optionSimps.OPTION_ss++pairSimps.PAIR_ss++patternMatchesLib.PMATCH_SIMP_ss++sumSimps.SUM_ss++boolSimps.literal_case_ss++BOOL_RED_ss);

(* TODO: arith_ss in bossLib adds PMATCH_SIMP_ss again... *)
val arith_multicore_ss = (std_multicore_ss++numSimps.ARITH_DP_ss++patternMatchesLib.PMATCH_SIMP_ss);

end
