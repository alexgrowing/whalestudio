import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrements
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
