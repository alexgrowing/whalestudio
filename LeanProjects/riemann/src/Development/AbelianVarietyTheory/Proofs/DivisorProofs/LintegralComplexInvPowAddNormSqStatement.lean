import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq : ∀ (m : ℕ) (a : ℝ), 0 < a → ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  first | exact @GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | exact GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | (intros; apply GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq <;> assumption)
