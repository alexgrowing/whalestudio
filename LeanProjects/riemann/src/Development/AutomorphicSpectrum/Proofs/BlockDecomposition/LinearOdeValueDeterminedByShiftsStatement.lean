import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_ode_value_determined_by_shifts : ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ, (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) → (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) → F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  first | exact @GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum | exact GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum | (intros; apply GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum <;> assumption)
