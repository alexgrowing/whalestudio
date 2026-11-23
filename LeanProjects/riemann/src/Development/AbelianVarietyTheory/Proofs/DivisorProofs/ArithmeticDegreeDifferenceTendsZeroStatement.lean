import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeDifferenceTendsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_degree_difference_tends_zero : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ B : ℝ, 2 ≤ B → ∀ u : D.what₂.Tau → Fin O.N → ℝ, Filter.Tendsto (fun R : ℝ => O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) - (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1))) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.ArDegIndep.limit_indep | exact GlobalTheory.ArDegIndep.limit_indep | (intros; apply GlobalTheory.ArDegIndep.limit_indep <;> assumption)
