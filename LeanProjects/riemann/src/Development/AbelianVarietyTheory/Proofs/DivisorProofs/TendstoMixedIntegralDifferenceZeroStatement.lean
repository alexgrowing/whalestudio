import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoMixedIntegralDifferenceZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_mixed_integral_difference_zero : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ B : ℝ, 2 ≤ B → ∀ u : Wt O.Y, (∀ τ, StrictAnti (u τ)) → ∀ (c : O.Y.Comp) (i : ℕ), i ≤ dimY O.Y → Tendsto (fun R : ℝ => (T.M c).int (fun k : Fin (dimY O.Y) => (T.K B c).c1 (if (k : ℕ) < i then T.L B c u + (T.K B c).ar ((T.F c).phR R u) else T.L B c u + (T.K B c).ar (psiOf h x' R u c))) ((T.F c).phR R u - psiOf h x' R u c)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.ArDegIndep.MixLimit.mixed_limit | exact GlobalTheory.ArDegIndep.MixLimit.mixed_limit | (intros; apply GlobalTheory.ArDegIndep.MixLimit.mixed_limit <;> assumption)
