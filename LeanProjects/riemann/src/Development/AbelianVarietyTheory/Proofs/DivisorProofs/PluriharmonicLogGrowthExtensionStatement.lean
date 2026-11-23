import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicLogGrowthExtension
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluriharmonic_log_growth_extension : ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (R r : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < r → r < R → R ≤ 1 → c i = 0 → i ∉ S → ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} → (∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) → ∀ w, levi f z w = 0) → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) → |f z| ≤ K - ε * ∑ k ∈ insert i S, Real.log ‖z k‖) → ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i) = f z := by
  first | exact @GlobalTheory.poissonInt_update_eq_of_levi_flat | exact GlobalTheory.poissonInt_update_eq_of_levi_flat | (intros; apply GlobalTheory.poissonInt_update_eq_of_levi_flat <;> assumption)
