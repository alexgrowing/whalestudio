import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousVanishingHyperplaneExtend
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_vanishing_hyperplane_extend : ∀ {k : ℕ} (b : A0 k) (L : Finset (A0 k)) (N : A0 k → ℂ), Continuous N → (∀ b' ∈ L, ∀ r : ℝ, b' ≠ r • b) →
  (∀ x, ⟪x, b⟫_ℝ = 0 → (∀ b' ∈ L, ⟪x, b'⟫_ℝ ≠ 0) → N x = 0) → ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0 := by
  first | exact @GlobalTheory.vanish_on_hyperplane_of_vanish_off_others | exact GlobalTheory.vanish_on_hyperplane_of_vanish_off_others | (intros; apply GlobalTheory.vanish_on_hyperplane_of_vanish_off_others <;> assumption)
