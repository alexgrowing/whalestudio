import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) := by
  first | exact @GlobalTheory.Henselisation.flat_hens | exact GlobalTheory.Henselisation.flat_hens | (intros; apply GlobalTheory.Henselisation.flat_hens <;> assumption)
