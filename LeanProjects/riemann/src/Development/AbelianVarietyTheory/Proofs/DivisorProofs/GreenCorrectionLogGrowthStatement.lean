import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCorrectionLogGrowth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_correction_log_growth : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ c : O.Y.Comp, ∃ C : ℝ, ∀ (u : Wt O.Y) (σ : Fin ((T.M c).n + 1)) (z : (T.M c).X σ), z ∉ (T.M c).Z σ → ∀ R : ℝ, 2 ≤ R → |psiOf h x' R u c σ z| ≤ C * ‖u‖ * Real.log ((T.M c).r σ z) := by
  first | exact @GlobalTheory.OtherInterpLog.abs_psiOf_le | exact GlobalTheory.OtherInterpLog.abs_psiOf_le | (intros; apply GlobalTheory.OtherInterpLog.abs_psiOf_le <;> assumption)
