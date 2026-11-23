import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapFlagArithDegreeChern
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_flag_arith_degree_chern : Hypotheses2 → HypothesesH → RegularAlteration → BunSt → ∀ G, Homog G → SwapFl G → OnObj fun _ O _ _ _ _ => ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → SwapEq O.Y G (O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R) O.Y.chern := by
  first | exact @GlobalTheory.SwapTrue.swapEq_true | exact GlobalTheory.SwapTrue.swapEq_true | (intros; apply GlobalTheory.SwapTrue.swapEq_true <;> assumption)
