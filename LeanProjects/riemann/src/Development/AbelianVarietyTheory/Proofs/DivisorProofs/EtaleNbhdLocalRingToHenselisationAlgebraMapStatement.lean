import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  first | exact @GlobalTheory.Henselisation.Hens.of_algebraMap | exact GlobalTheory.Henselisation.Hens.of_algebraMap | (intros; apply GlobalTheory.Henselisation.Hens.of_algebraMap <;> assumption)
