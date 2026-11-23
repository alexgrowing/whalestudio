import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n, GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  first | exact @GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | exact GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv <;> assumption)
