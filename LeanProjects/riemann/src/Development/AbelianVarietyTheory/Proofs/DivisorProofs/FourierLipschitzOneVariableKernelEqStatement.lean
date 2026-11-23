import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ), 𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  first | exact @GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | exact GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | (intros; apply GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow <;> assumption)
