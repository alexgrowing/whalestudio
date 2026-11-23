import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableBoundedMulOfSummableNormSq
import Mathlib
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div : ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq | exact GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq | (intros; apply GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq <;> assumption)
