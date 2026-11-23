import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegral
import Mathlib
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) → ∀ (g : Ω ≃ₐ[R] Ω) (x : Ω), v (g x) = v x := by
  first | exact @GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | exact GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | (intros; apply GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral <;> assumption)
