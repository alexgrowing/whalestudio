import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralNormSqMobDMulCompMob
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ → ℝ, ∫ a : ℂ, Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g a) = ∫ b : ℂ, f b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob <;> assumption)
