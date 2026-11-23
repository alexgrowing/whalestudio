import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  first | exact @GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | exact GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | (intros; apply GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv <;> assumption)
