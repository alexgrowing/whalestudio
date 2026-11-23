import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowth
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
