import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_div_pow_of_choose_bounds : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  first | exact @GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | exact GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | (intros; apply GlobalTheory.tendsto_rank_div_pow_of_choose_bounds <;> assumption)
