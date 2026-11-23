import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  first | exact @GlobalTheory.ChernCalc.integral_chernF_mul_grF | exact GlobalTheory.ChernCalc.integral_chernF_mul_grF | (intros; apply GlobalTheory.ChernCalc.integral_chernF_mul_grF <;> assumption)
