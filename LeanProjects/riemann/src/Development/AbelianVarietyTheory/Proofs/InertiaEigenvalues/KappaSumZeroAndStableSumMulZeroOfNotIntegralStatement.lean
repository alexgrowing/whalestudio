import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) → InvAlg.kapSum B₁ B₂ = 0 ∧ B₁.stSum * B₂.stSum = 0 := by
  first | exact @GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | exact GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | (intros; apply GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral <;> assumption)
