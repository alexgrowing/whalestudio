import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

theorem sp_coef_map {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] M) (ψ : N →ₗ[ℂ] ℂ) (x : M ⊗[ℂ] N) :
    TensorProduct.rid ℂ M (ψ.lTensor M (TensorProduct.map f LinearMap.id x)) =
      f (TensorProduct.rid ℂ M (ψ.lTensor M x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sp_expand {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : M ⊗[ℂ] N) :
    x = ∑ i, TensorProduct.rid ℂ M (((Module.finBasis ℂ N).coord i).lTensor M x) ⊗ₜ
      (Module.finBasis ℂ N) i := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight (Module.finBasis ℂ N)).symm_apply_apply x]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp_rw [TensorProduct.equivFinsuppOfBasisRight_apply]

theorem sp_tmul_cancel {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [AddCommGroup N]
    [Module ℂ N] {w : E} (hw : ‖w‖ = 1) {y z : N} (h : w ⊗ₜ[ℂ] y = w ⊗ₜ[ℂ] z) : y = z := by
  have e := congrArg (fun u => TensorProduct.lid ℂ N
    (((innerSL ℂ w : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ).rTensor N u)) h
  simpa [hw] using e

variable {p q : ℕ} {Λ1 : Fin p → ℝ} {Λ2 : Fin q → ℝ}

theorem sp_left (T1 : KType (fun _ : Fin p => true) Λ1) {N : Type*} [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : T1.V ⊗[ℂ] N) (ν : Fin p → ℝ)
    (hw : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν r : ℝ) : ℂ) • x)
    (hr : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0) :
    ∃ y : N, x = T1.w ⊗ₜ y := by
  have hcoef : ∀ i, ∃ c : ℂ,
      TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = c • T1.w := by
    intro i
    by_cases hm : TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = 0
    · exact ⟨0, by rw [hm, zero_smul]⟩
    · have h : IsKHWVec (fun _ : Fin p => true) (kunits T1) ν
          (TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x)) := by
        refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
        · rw [← sp_coef_map, hw r, map_smul, map_smul]
        · rw [← sp_coef_map, hr r s hrs, map_zero, map_zero]
      obtain ⟨-, c, hc⟩ := KType.hw_unique T1 hm h
      exact ⟨c, hc⟩
  choose c hc using hcoef
  refine ⟨∑ i, c i • (Module.finBasis ℂ N) i, ?_⟩
  conv_lhs => rw [sp_expand x]
  simp_rw [hc, TensorProduct.smul_tmul, TensorProduct.tmul_sum]

theorem sp_ker (T1 : KType (fun _ : Fin p => true) Λ1) (T2 : KType (fun _ : Fin q => true) Λ2)
    (x : T1.V ⊗[ℂ] T2.V) (hx0 : x ≠ 0) (ν1 : Fin p → ℝ) (ν2 : Fin q → ℝ)
    (hw1 : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν1 r : ℝ) : ℂ) • x)
    (hr1 : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0)
    (hw2 : ∀ r, TensorProduct.map LinearMap.id (kunits T2 r r) x = ((ν2 r : ℝ) : ℂ) • x)
    (hr2 : ∀ r s, r < s → TensorProduct.map LinearMap.id (kunits T2 r s) x = 0) :
    ∃ c : ℂ, x = c • (T1.w ⊗ₜ T2.w) := by
  obtain ⟨y, rfl⟩ := sp_left T1 x ν1 hw1 hr1
  have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (TensorProduct.tmul_zero _ _)
  have h : IsKHWVec (fun _ : Fin q => true) (kunits T2) ν2 y := by
    refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
    · have e := hw2 r
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul] at e
      exact sp_tmul_cancel T1.w_norm e
    · have e := hr2 r s hrs
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_zero T2.V T1.w] at e
      exact sp_tmul_cancel T1.w_norm e
  obtain ⟨-, c, hc⟩ := KType.hw_unique T2 hy0 h
  exact ⟨c, by rw [hc, TensorProduct.tmul_smul]⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
