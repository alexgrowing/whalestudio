import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCompHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_comp_holomorphic : ∀ {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}, DifferentiableAt ℂ φ v → DifferentiableAt ℝ c (φ v) → ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a = pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  first | exact @GlobalTheory.CxForm.sum_dbar_comp_smul_dzb | exact GlobalTheory.CxForm.sum_dbar_comp_smul_dzb | (intros; apply GlobalTheory.CxForm.sum_dbar_comp_smul_dzb <;> assumption)
