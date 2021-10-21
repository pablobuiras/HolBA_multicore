open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open bir_promisingTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;

open bisimulationTheory;

val _ = new_theory "refinement";

Definition rel_simulation_def:
SIMULATION R step_a step_c =
!s t t'.
R s t /\ step_c t t' ==>
?s'. step_a s s' /\ R s' t'
End;

Definition step_aux_def:
parstep_2state (cores1,M1) (cores2,M2) = parstep cores1 M1 cores2 M2
End;

Definition bir_simulation_def:
BIR_SIMULATION R =
SIMULATION R parstep_2state parstep_2state
End;

Definition identity_refinement_def:
ID_R s t = (s = t)
End;

Theorem identity_refinement_eq:
   !s. ID_R s s
Proof
 fs [identity_refinement_def]
QED;

Theorem id_simulation:
BIR_SIMULATION ID_R
Proof
 fs [bir_simulation_def, rel_simulation_def, identity_refinement_def]
QED;

val _ = export_theory ();
