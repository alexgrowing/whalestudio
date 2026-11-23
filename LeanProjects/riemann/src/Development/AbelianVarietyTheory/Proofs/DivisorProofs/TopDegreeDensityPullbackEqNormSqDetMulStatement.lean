import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (ω : GlobalTheory.CxForm.Alt n), GlobalTheory.CxForm.dens (GlobalTheory.CxForm.pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * GlobalTheory.CxForm.dens ω := by
  first | exact @GlobalTheory.CxForm.dens_pull | exact GlobalTheory.CxForm.dens_pull | (intros; apply GlobalTheory.CxForm.dens_pull <;> assumption)
