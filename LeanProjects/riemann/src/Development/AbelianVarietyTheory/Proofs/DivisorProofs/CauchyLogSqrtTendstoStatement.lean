import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyLogSqrtTendsto
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_log_sqrt_tendsto : ∀ (F : ℝ → ℝ) (C R₀ : ℝ) (d : ℕ), (∀ R R' : ℝ, R₀ ≤ R → R ≤ R' → |F R - F R'| ≤ C * Real.log R ^ d / Real.sqrt R) → ∃ L, Tendsto F atTop (𝓝 L) := by
  first | exact @GlobalTheory.Mean4Cauchy.exists_tendsto_of_log_pow_div_sqrt | exact GlobalTheory.Mean4Cauchy.exists_tendsto_of_log_pow_div_sqrt | (intros; apply GlobalTheory.Mean4Cauchy.exists_tendsto_of_log_pow_div_sqrt <;> assumption)
