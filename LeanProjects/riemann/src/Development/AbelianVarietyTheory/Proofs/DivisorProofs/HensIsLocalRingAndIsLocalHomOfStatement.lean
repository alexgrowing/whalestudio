import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | exact GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | (intros; apply GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of <;> assumption)
