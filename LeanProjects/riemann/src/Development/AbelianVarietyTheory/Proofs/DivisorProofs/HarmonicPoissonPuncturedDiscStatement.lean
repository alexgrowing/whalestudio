import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPoissonPuncturedDisc
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_poisson_punctured_disc : ∀ (R : ℝ) (f : ℂ → ℝ), 0 < R → R ≤ 1 → InnerProductSpace.HarmonicOnNhd f (Metric.closedBall 0 R \ {0}) → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) R, z ≠ 0 → |f z| ≤ K - ε * Real.log ‖z‖) → ∀ w ∈ Metric.ball (0 : ℂ) R, w ≠ 0 → f w = ReciprocityTheory.AnForm.A.poissonInt f R w := by
  first | exact @GlobalTheory.harmonic_punctured_eq_poissonInt | exact GlobalTheory.harmonic_punctured_eq_poissonInt | (intros; apply GlobalTheory.harmonic_punctured_eq_poissonInt <;> assumption)
