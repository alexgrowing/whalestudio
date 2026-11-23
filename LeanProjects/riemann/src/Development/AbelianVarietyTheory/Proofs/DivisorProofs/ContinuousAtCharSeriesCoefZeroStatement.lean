import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
