import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsDirected (EtNbhd R) (· ≤ ·) := by
  first | exact @GlobalTheory.Henselisation.etNbhd_isDirected | exact GlobalTheory.Henselisation.etNbhd_isDirected | (intros; apply GlobalTheory.Henselisation.etNbhd_isDirected <;> assumption)
