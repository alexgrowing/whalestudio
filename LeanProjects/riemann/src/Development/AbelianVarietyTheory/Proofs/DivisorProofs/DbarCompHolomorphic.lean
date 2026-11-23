import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem sum_dbar_comp_smul_dzb {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}
    (hφ : DifferentiableAt ℂ φ v) (hc : DifferentiableAt ℝ c (φ v)) :
    ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a =
      pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  have key (w : V m) : GlobalTheory.dbar c (φ v) w = ∑ b, GlobalTheory.dbar c (φ v) (coordVec b) * conj (w b) := by
    have hw : w = ∑ b, w b • coordVec b := by
      simpa using ((EuclideanSpace.basisFun (Fin m) ℂ).sum_repr w).symm
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smulₛₗ, smul_eq_mul, mul_comm]
  rw [map_sum]
  simp only [map_smul, (pull_dz _ _).2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.dbar_comp_holo hc hφ, key, Finset.sum_smul]

end GlobalTheory.CxForm
