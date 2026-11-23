import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricChernIntegralEval
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_metric_chern_integral_eval : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (X : GlobalTheory.ProjVar.Var ℚ) (E : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf X) m 0), X.dim = 0 → ∃ (σ : ℚ →+* ℂ) (H : GlobalTheory.FlagBundle.Mat m X.Fn → CxPts X.str σ → GlobalTheory.FlagBundle.Mat m ℂ), GlobalTheory.GoodMetric.IsMetricOn E ⊤ H ∧ GlobalTheory.GoodMetric.IsGood E ⊤ H ∧ ∀ (R : MvPolynomial (ι × ℕ) ℝ) (t : ℝ), GlobalTheory.GoodMetric.HasChernIntegral E ⊤ H R t → t = MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
  first | exact @GlobalTheory.GoodMetric.PointChern.chernIntegral_point | exact GlobalTheory.GoodMetric.PointChern.chernIntegral_point | (intros; apply GlobalTheory.GoodMetric.PointChern.chernIntegral_point <;> assumption)
