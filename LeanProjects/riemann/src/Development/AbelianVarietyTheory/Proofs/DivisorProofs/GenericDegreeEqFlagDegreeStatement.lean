import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreeEqFlagDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_eq_flag_degree : Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N) := by
  first | exact @GlobalTheory.FlagDegChecked.flag_gdeg_eq_degFl_checked | exact GlobalTheory.FlagDegChecked.flag_gdeg_eq_degFl_checked | (intros; apply GlobalTheory.FlagDegChecked.flag_gdeg_eq_degFl_checked <;> assumption)
