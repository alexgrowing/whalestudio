import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], HenselianLocalRing (Hens R) := by
  first | exact @GlobalTheory.Henselisation.henselianLocalRing_hens | exact GlobalTheory.Henselisation.henselianLocalRing_hens | (intros; apply GlobalTheory.Henselisation.henselianLocalRing_hens <;> assumption)
