import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAsymptoticExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_asymptotic_exists : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), 0 < Y.vol → ShapeF Φ hh → Change Φ → ∀ B₀ : ℝ, 2 ≤ B₀ → ∃ a b : ℝ, ExactAt Φ hh B₀ a b := by
  first | exact @GlobalTheory.Mean4.exists_exactAt | exact GlobalTheory.Mean4.exists_exactAt | (intros; apply GlobalTheory.Mean4.exists_exactAt <;> assumption)
