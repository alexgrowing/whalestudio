import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.LineForm

theorem chain_sum_coordVec {n : ℕ} (w : V n) : w = ∑ b, w b • coordVec b := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem del_dbar_comp_holo_pull : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m),
    DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  intro m n τ c v hτ hc
  constructor
  · simp only [del_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
    simp only [map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]
  · simp only [dbar_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
    simp only [map_sum, map_smulₛₗ, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

end GlobalTheory.LineForm
