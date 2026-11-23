import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, EuclideanSpace.single_apply, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]
    simp [map_sum, map_smul, smul_eq_mul]
  simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
