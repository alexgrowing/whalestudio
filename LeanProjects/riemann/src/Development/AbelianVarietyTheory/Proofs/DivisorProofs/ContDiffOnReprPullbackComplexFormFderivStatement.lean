import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  first | exact @GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | exact GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | (intros; apply GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv <;> assumption)
