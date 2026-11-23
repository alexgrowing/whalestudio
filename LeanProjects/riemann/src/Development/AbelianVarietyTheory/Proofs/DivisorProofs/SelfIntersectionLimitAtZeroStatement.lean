import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLimitAtZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_limit_at_zero : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), Agree A → ∀ B : ℝ, 2 ≤ B → ∀ u : Wt Y, IsRat Y u → RegDom u → ∀ c, Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c) (𝓝[>] (0 : ℚ)) (𝓝 (evS Y (A.Ps B c) u 0)) := by
  first | exact @GlobalTheory.Mean4.tendsto_arSelfC_of_agree | exact GlobalTheory.Mean4.tendsto_arSelfC_of_agree | (intros; apply GlobalTheory.Mean4.tendsto_arSelfC_of_agree <;> assumption)
