import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThresholdAndLogComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threshold_and_log_comparison : ∀ (D : D7) (Y : ShimX D.what₂.Tau), 2 < D.R.f * (Y.N - 1) → (∀ u g, WeightHyp Y u g → 48 ≤ bigB0 Y u g) ∧ 1 ≤ D.host.rdE ∧ ∀ B : ℝ, 1 ≤ B → Real.log B ≤ lg D B := by
  first | exact @GlobalTheory.Mean4.threshold_ge_and_rootDiscr_ge | exact GlobalTheory.Mean4.threshold_ge_and_rootDiscr_ge | (intros; apply GlobalTheory.Mean4.threshold_ge_and_rootDiscr_ge <;> assumption)
