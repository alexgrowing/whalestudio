import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPointedEtaleNeighbourhoodEqMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | exact GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | (intros; apply GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map <;> assumption)
