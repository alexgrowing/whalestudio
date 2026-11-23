import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusChangeOfVariablesPair
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_change_of_variables_pair : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main <;> assumption)
