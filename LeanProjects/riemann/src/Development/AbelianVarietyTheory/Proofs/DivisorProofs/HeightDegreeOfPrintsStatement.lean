import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDegreeOfPublished
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_degree_of_hypotheses : Hypotheses2 → HypothesesH → OnObj fun _ _ _ T _ _ => TieDeg T := by
  first | exact @GlobalTheory.DegreeOnObjects.tieDeg_onObj | exact GlobalTheory.DegreeOnObjects.tieDeg_onObj | (intros; apply GlobalTheory.DegreeOnObjects.tieDeg_onObj <;> assumption)
