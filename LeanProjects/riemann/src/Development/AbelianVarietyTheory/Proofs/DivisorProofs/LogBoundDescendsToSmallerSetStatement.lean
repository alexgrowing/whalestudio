import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBoundDescendsToSmallerSet
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_bound_descends_to_smaller_set : ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (R r : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < r → r < R → c i = 0 → i ∉ S → ContinuousOn f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) → |f z| ≤ K - ε * ∑ k ∈ insert i S, Real.log ‖z k‖) → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → |ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i)| ≤ K - ε * ∑ k ∈ S, Real.log ‖z k‖ := by
  first | exact @GlobalTheory.poissonInt_update_bound | exact GlobalTheory.poissonInt_update_bound | (intros; apply GlobalTheory.poissonInt_update_bound <;> assumption)
