import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPotentialTruncation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_potential_truncation : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ R : ℝ, 2 ≤ R → ∀ (u : Wt O.Y) (c : O.Y.Comp), (T.M c).Smooth (psiOf h x' R u c) := by
  first | exact @GlobalTheory.ArDegIndep.psiOf_smooth | exact GlobalTheory.ArDegIndep.psiOf_smooth | (intros; apply GlobalTheory.ArDegIndep.psiOf_smooth <;> assumption)
