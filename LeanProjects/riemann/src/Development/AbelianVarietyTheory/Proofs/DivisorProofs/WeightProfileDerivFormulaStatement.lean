import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightProfileDerivFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightProfile_deriv_formula : ∀ (χ : ℝ → ℝ), IsCutoff χ → ∀ (κ L t u : ℝ), 0 < L → 0 < u → ContDiffAt ℝ 2 (weightProfile χ κ L t) u ∧ deriv (weightProfile χ κ L t) u = t * (deriv χ (u / L) / L * logisticFactor κ L u + χ (u / L) * (-κ * logisticFactor κ L u * (1 - logisticFactor κ L u))) ∧ deriv (deriv (weightProfile χ κ L t)) u = t * (deriv (deriv χ) (u / L) / L ^ 2 * logisticFactor κ L u + 2 * (deriv χ (u / L) / L) * (-κ * logisticFactor κ L u * (1 - logisticFactor κ L u)) + χ (u / L) * (κ ^ 2 * logisticFactor κ L u * (1 - logisticFactor κ L u) * (1 - 2 * logisticFactor κ L u))) := by
  first | exact @GlobalTheory.InterpCurv.weightProfile_second_deriv | exact GlobalTheory.InterpCurv.weightProfile_second_deriv | (intros; apply GlobalTheory.InterpCurv.weightProfile_second_deriv <;> assumption)
