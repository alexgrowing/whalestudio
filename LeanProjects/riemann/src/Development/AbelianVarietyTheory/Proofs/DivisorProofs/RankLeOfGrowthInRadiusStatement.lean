import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadius
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ → (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) → (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) → ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  first | exact @GlobalTheory.rank_le_of_growth_in_radius | exact GlobalTheory.rank_le_of_growth_in_radius | (intros; apply GlobalTheory.rank_le_of_growth_in_radius <;> assumption)
