import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormTwoSidedBound
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_form_two_sided_bound : ∀ {e : ℕ} (F : (Fin e → ℂ) → (Fin e → ℂ) → ℝ) (S : Set (Fin e → ℂ)), IsCompact S → ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) => F p.1 p.2) (S ×ˢ Set.univ) → (∀ z ∈ S, ∀ w, w ≠ 0 → 0 < F z w) → (∀ z w (t : ℝ), F z (t • w) = t ^ 2 * F z w) → ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ z ∈ S, ∀ w, δ * ∑ k, ‖w k‖ ^ 2 ≤ F z w ∧ F z w ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  first | exact @GlobalTheory.quadForm_comparable_sumSq | exact GlobalTheory.quadForm_comparable_sumSq | (intros; apply GlobalTheory.quadForm_comparable_sumSq <;> assumption)
