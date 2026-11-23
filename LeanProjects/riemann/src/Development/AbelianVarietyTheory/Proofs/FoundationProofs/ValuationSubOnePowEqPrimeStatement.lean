import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L, IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | exact GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | (intros; apply GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime <;> assumption)
