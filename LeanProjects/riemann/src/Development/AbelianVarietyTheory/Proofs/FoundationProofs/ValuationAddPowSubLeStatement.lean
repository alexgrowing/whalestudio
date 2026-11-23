import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLe
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ y β : L, v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.valuation_add_pow_sub_le | exact GlobalTheory.AlmostEt.valuation_add_pow_sub_le | (intros; apply GlobalTheory.AlmostEt.valuation_add_pow_sub_le <;> assumption)
