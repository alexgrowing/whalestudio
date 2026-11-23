import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_pullback_holomorphic_zero : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U → DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m), dbarAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 := by
  first | exact @GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | exact GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv <;> assumption)
