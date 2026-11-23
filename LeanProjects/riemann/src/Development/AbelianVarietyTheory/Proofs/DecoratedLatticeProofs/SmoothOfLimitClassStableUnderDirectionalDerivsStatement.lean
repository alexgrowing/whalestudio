import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | exact GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | (intros; apply GlobalTheory.contDiff_of_class_tendstoLocallyUniformly <;> assumption)
