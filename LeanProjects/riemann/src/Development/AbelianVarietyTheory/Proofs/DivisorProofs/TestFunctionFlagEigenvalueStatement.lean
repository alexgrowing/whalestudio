import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionFlagEigenvalue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_flag_eigenvalue : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ArDegree → ArCalc → RegularAlteration → ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (hh : Fn Y), GlobalTheory.FlagZ.IsHh D.what₂.Tau Y.N hh → hh (testF Y) = (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j) - 1) * testI Y := by
  first | exact @GlobalTheory.CovTest.hh_testF | exact GlobalTheory.CovTest.hh_testF | (intros; apply GlobalTheory.CovTest.hh_testF <;> assumption)
