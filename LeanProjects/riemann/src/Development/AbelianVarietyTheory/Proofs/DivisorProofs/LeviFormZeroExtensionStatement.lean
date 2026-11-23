import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormZeroExtension
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_form_zero_extension : ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (r : ℝ) (f g : (Fin e → ℂ) → ℝ), ContDiffOn ℝ ∞ g {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → g z = f z) → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → ∀ w, levi f z w = 0) → ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → ∀ w, levi g z w = 0 := by
  first | exact @GlobalTheory.levi_eq_zero_of_eq_off_coord_hyperplane | exact GlobalTheory.levi_eq_zero_of_eq_off_coord_hyperplane | (intros; apply GlobalTheory.levi_eq_zero_of_eq_off_coord_hyperplane <;> assumption)
