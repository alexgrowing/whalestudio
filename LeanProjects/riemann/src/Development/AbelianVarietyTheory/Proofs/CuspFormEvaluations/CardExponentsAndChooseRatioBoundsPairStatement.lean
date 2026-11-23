import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BinomRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  first | exact @GlobalTheory.card_exponents_and_choose_ratio_bounds | exact GlobalTheory.card_exponents_and_choose_ratio_bounds | (intros; apply GlobalTheory.card_exponents_and_choose_ratio_bounds <;> assumption)
