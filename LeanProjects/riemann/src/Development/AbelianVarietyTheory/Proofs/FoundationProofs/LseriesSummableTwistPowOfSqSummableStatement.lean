import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummable
import Mathlib
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | exact GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | (intros; apply GlobalTheory.lseriesSummable_twist_pow_of_sq_summable <;> assumption)
