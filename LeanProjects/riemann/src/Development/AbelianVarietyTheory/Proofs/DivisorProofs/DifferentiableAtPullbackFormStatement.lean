import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtPullbackForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_pullback_form : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U → DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun x => (bas n).repr (pull (fderiv ℂ φ x) θ) S) v := by
  first | exact @GlobalTheory.PullCoefDiff.differentiableAt_repr_pull_fderiv | exact GlobalTheory.PullCoefDiff.differentiableAt_repr_pull_fderiv | (intros; apply GlobalTheory.PullCoefDiff.differentiableAt_repr_pull_fderiv <;> assumption)
