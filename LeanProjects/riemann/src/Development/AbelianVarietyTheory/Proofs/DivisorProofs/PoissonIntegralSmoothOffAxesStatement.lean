import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoissonIntegralSmoothOffAxes
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_integral_smooth_off_axes : ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (R r : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < r → r < R → c i = 0 → ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} → ContDiffOn ℝ ∞ (fun z => ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i)) {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} := by
  first | exact @GlobalTheory.CirclePoissonParam.poissonInt_update_contDiffOn | exact GlobalTheory.CirclePoissonParam.poissonInt_update_contDiffOn | (intros; apply GlobalTheory.CirclePoissonParam.poissonInt_update_contDiffOn <;> assumption)
