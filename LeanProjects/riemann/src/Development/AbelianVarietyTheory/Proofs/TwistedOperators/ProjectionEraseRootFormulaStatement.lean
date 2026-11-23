import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionEraseRootFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_erase_root_formula : ∀ {k : ℕ} {T : Finset (SV k)} {u : SV k}, IsPar T → u ∈ T → ∀ x : A0 k,
  pr T x = pr (T.erase u) x + (⟪rt T u, x⟫_ℝ / ‖rt T u‖ ^ 2) • rt T u := by
  first | exact @GlobalTheory.pr_eq_pr_erase_add_rt | exact GlobalTheory.pr_eq_pr_erase_add_rt | (intros; apply GlobalTheory.pr_eq_pr_erase_add_rt <;> assumption)
