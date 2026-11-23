import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLinearCoefficient
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_bound_linear_coefficient : ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ∀ B₀ a b : ℝ, 48 ≤ B₀ → 0 < Y.vol → Propor Y → FewBad Y → TestVal Φ hh r → ExactAt Φ hh B₀ a b → -a ≤ C * (Real.log B₀ + Real.log D.host.rdE) := by
  first | exact @GlobalTheory.Mean4.neg_first_coeff_le_log | exact GlobalTheory.Mean4.neg_first_coeff_le_log | (intros; apply GlobalTheory.Mean4.neg_first_coeff_le_log <;> assumption)
