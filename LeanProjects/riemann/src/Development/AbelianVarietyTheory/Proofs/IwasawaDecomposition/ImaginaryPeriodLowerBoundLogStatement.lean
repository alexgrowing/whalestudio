import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImaginaryPeriodLowerBoundLog
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
open GlobalTheory.ShFam.Hor
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imaginary_period_lower_bound_log : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → ∃ (c : ℝ) (k : ℕ), 0 < c ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ∀ v : Fin d → ℝ, c * ‖v‖ ^ 2 ≤ (1 + ‖s‖) ^ k * (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im := by
  first | exact @GlobalTheory.period_im_lower_bound | exact GlobalTheory.period_im_lower_bound | (intros; apply GlobalTheory.period_im_lower_bound <;> assumption)
