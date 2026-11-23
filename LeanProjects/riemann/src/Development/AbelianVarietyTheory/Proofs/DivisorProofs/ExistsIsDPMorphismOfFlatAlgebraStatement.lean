import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isDPMorphism_of_flat_algebra : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I), ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  first | exact @GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | exact GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | (intros; apply GlobalTheory.DPFlat.exists_isDPMorphism_of_flat <;> assumption)
