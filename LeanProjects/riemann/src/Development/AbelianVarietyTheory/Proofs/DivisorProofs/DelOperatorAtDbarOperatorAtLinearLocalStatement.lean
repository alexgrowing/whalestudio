import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  first | exact @GlobalTheory.CxForm.delAt_dbarAt_linear_local | exact GlobalTheory.CxForm.delAt_dbarAt_linear_local | (intros; apply GlobalTheory.CxForm.delAt_dbarAt_linear_local <;> assumption)
