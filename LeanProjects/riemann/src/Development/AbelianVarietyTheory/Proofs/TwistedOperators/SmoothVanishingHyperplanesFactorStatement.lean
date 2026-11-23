import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVanishingHyperplanesFactor
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vanishing_hyperplanes_factor : ∀ {k : ℕ} (L : Finset (A0 k)) (N : A0 k → ℂ), (∀ b ∈ L, b ≠ 0) → (∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → ∀ r : ℝ, b' ≠ r • b) →
  ContDiff ℝ ∞ N → (∀ b ∈ L, ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0) →
  ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, N x = (∏ b ∈ L, (⟪x, b⟫_ℝ : ℂ)) * F x := by
  first | exact @GlobalTheory.smooth_div_prod_linear_forms | exact GlobalTheory.smooth_div_prod_linear_forms | (intros; apply GlobalTheory.smooth_div_prod_linear_forms <;> assumption)
