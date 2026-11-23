import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedOrbitSumCongrCoefficientRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitSum_congr_coefficientRing : ∀ {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A] (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A)), (∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) → (∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L') → intUnits O A ⊓ G = intUnits O' A ⊓ G → orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  first | exact @GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | exact GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | (intros; apply GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe <;> assumption)
