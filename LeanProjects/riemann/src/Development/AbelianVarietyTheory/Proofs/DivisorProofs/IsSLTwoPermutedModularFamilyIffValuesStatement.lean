import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValues
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ), f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  first | exact @GlobalTheory.QFam.isFam_iff_values | exact GlobalTheory.QFam.isFam_iff_values | (intros; apply GlobalTheory.QFam.isFam_iff_values <;> assumption)
