import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsChooseSmallPadicValAxInduction
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_choose_small_padicVal_ax_induction : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N → ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  first | exact @GlobalTheory.exists_choose_small_valuation_ax | exact GlobalTheory.exists_choose_small_valuation_ax | (intros; apply GlobalTheory.exists_choose_small_valuation_ax; all_goals assumption)
