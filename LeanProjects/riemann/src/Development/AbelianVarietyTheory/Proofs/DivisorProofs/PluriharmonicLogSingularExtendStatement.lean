import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicLogSingularExtend
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluriharmonic_log_singular_extend : ∀ (e : ℕ) (S : Finset (Fin e)) (c : Fin e → ℂ) (R : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < R → R ≤ 1 → (∀ i ∈ S, c i = 0) → ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ i ∈ S, z i ≠ 0} → (∀ z ∈ Metric.ball c R, (∀ i ∈ S, z i ≠ 0) → ∀ w, levi f z w = 0) → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ i ∈ S, z i ≠ 0) → |f z| ≤ K - ε * ∑ i ∈ S, Real.log ‖z i‖) → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ g (Metric.ball c ρ) ∧ ∀ z ∈ Metric.ball c ρ, (∀ i ∈ S, z i ≠ 0) → g z = f z := by
  first | exact @GlobalTheory.FlatExt.flat_extend | exact GlobalTheory.FlatExt.flat_extend | (intros; apply GlobalTheory.FlatExt.flat_extend <;> assumption)
