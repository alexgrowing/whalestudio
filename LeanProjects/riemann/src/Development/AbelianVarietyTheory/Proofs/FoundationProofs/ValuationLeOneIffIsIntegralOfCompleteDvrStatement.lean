import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr : ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  first | exact @GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | exact GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | (intros; apply GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr <;> assumption)
