import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeAsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_degree_as_integral : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → ∀ c, O.Y.geoC (O.Y.Mbar B u s) c = (T.M c).int (fun _ => (T.F c).form (A.sh u s) s 0) (fun _ _ => 1) := by
  first | exact @GlobalTheory.GeoCObj.geoC_onObj | exact GlobalTheory.GeoCObj.geoC_onObj | (intros; apply GlobalTheory.GeoCObj.geoC_onObj <;> assumption)
