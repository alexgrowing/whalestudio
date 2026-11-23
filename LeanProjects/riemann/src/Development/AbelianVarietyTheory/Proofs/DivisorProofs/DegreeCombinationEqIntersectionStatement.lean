import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeCombinationEqIntersection
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
theorem _root_.GlobalTheory.T.degree_combination_eq_intersection : GlobalTheory.Published.ChernDegree → ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) → ∀ (gr : ι × Fin N → Y.Dv), (∀ x, ∃ r, GlobalTheory.Cartier.Presents (gr x) ((GlobalTheory.FlagZ.grLine x).B.pull j) r) → ∀ n : ι × Fin N → ℤ, gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) Y.dim = ((Y.inter fun _ => ∑ x, n x • gr x : ℤ) : ℝ) := by
  first | exact @GlobalTheory.FlagDeg.gdeg_comb_grLine | exact GlobalTheory.FlagDeg.gdeg_comb_grLine | (intros; apply GlobalTheory.FlagDeg.gdeg_comb_grLine <;> assumption)
