import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogSwapSymmetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homog_swap_symmetric : ArCalc → RegularAlteration → ∃ G, Homog G ∧ Swap2 G := by
  first | exact @GlobalTheory.CovTest.homog_swap_exists_of_ar_calc | exact GlobalTheory.CovTest.homog_swap_exists_of_ar_calc | (intros; apply GlobalTheory.CovTest.homog_swap_exists_of_ar_calc <;> assumption)
