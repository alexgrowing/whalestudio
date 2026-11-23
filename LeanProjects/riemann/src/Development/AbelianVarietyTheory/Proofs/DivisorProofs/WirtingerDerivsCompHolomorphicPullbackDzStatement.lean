import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wirtingerDerivs_comp_holomorphic_pullback_dz : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m), DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m) = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m) = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  first | exact @GlobalTheory.LineForm.del_dbar_comp_holo_pull | exact GlobalTheory.LineForm.del_dbar_comp_holo_pull | (intros; apply GlobalTheory.LineForm.del_dbar_comp_holo_pull <;> assumption)
