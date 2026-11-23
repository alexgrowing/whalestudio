import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ) (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) → (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) → GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v = ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  first | exact @GlobalTheory.CxForm.DelForm.delAt_sum_smul | exact GlobalTheory.CxForm.DelForm.delAt_sum_smul | (intros; apply GlobalTheory.CxForm.DelForm.delAt_sum_smul <;> assumption)
