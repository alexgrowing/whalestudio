import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorDbarOperatorPullbackConstantFormHolom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delOperator_dbarOperator_pullback_constantForm_holomorphic : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ v ∈ U, delAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 ∧ dbarAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 := by
  first | exact @GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv | exact GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv <;> assumption)
