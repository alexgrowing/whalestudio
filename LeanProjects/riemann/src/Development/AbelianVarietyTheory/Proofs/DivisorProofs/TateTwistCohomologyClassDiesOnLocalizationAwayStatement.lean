import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAway
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) → ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 → ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'), ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.AwayCont.kill_of_loc) | (exact GlobalTheory.EtC.AwayCont.kill_of_loc) | (intros; apply GlobalTheory.EtC.AwayCont.kill_of_loc <;> assumption)
