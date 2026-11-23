import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffDerivBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_deriv_bound : ∀ χ : ℝ → ℝ, IsCutoff χ → ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → |deriv χ y| ≤ M ∧ |deriv (deriv χ) y| ≤ M ∧ deriv χ y ^ 2 ≤ M * χ y := by
  first | exact @GlobalTheory.cutoff_deriv_bounds | exact GlobalTheory.cutoff_deriv_bounds | (intros; apply GlobalTheory.cutoff_deriv_bounds <;> assumption)
