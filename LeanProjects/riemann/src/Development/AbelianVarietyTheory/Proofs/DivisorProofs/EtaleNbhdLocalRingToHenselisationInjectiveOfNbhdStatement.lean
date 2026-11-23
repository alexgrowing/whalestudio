import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Function.Injective (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | exact GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | (intros; apply GlobalTheory.Henselisation.Hens.of_injective_of_nbhd <;> assumption)
