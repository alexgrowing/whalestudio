import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormGradientLeviIdentity
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_gradient_levi_identity : ∀ {e : ℕ} (h : (Fin e → ℂ) → ℂ) (Φ N : (Fin e → ℂ) → ℝ) (z w : Fin e → ℂ), AnalyticAt ℂ h z → h z ≠ 0 → ContDiffAt ℝ 2 Φ z → N =ᶠ[nhds z] (fun y => ‖h y‖ ^ 2 * Real.exp (-2 * Φ y)) → ((fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z w) ^ 2 + (fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z (Complex.I • w)) ^ 2) / 4 * N z = levi N z w + 2 * N z * levi Φ z w := by
  first | exact @GlobalTheory.LeviGradCoord.grad_sq_mul_eq_levi | exact GlobalTheory.LeviGradCoord.grad_sq_mul_eq_levi | (intros; apply GlobalTheory.LeviGradCoord.grad_sq_mul_eq_levi <;> assumption)
