import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace SchurDetBound

theorem qf_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (G : Matrix ι ι ℝ)
    (w : κ → ℝ) : MCSchur.qf G (w ∘ e) = MCSchur.qf (reindex e e G) w := by
  simp only [MCSchur.qf, dotProduct, mulVec, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp

end SchurDetBound

theorem SchurDetBound.proof : SchurDetBound.Statement := by
  intro k G hsym hdet t ht
  set e : Fin (k + 1) ≃ Fin k ⊕ Fin 1 := finSumFinEquiv.symm with he
  set M := reindex e e G with hMdef
  set A := M.toBlocks₁₁ with hAdef
  set B := M.toBlocks₁₂ with hBdef
  set D := M.toBlocks₂₂ with hDdef
  have hA : A = G.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [hAdef, hMdef, he, toBlocks₁₁, Fin.castSucc]
  have hAsymm : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hAdef, hMdef, toBlocks₁₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hM : fromBlocks A B Bᴴ D = M := by
    rw [← fromBlocks_toBlocks M]
    congr 1
    rw [conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hBdef, hMdef, toBlocks₁₂, toBlocks₂₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hdetA : 0 < A.det := by rw [hA]; exact hdet
  have : Invertible A := invertibleOfIsUnitDet A hdetA.ne'.isUnit
  set S := D - Bᴴ * A⁻¹ * B with hSdef
  have hdetG : G.det = A.det * S 0 0 := by
    rw [← det_reindex_self e G, ← hMdef, ← hM, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
      Matrix.det_unique (D - Bᴴ * A⁻¹ * B)]
    rfl

  set y : Fin 1 → ℝ := fun _ => 1 with hy
  set x : Fin k → ℝ := -((A⁻¹ * B) *ᵥ y) with hx
  have hval : MCSchur.qf G ((Sum.elim x y) ∘ e) = S 0 0 := by
    rw [SchurDetBound.qf_reindex, ← hMdef, ← hM]
    have h := schur_complement_eq₁₁ B D x y hAsymm
    simp only [star_trivial] at h
    simp only [MCSchur.qf, dotProduct_mulVec]
    rw [show (Sum.elim x y) = x ⊕ᵥ y from rfl, h, hx, neg_add_cancel]
    simp [hy, dotProduct, vecMul, hSdef]
  have hlast : ((Sum.elim x y) ∘ e) (Fin.last k) = 1 := by
    simp [he, hy]
  have hts := ht _ hlast
  rw [hval] at hts
  rw [hdetG, ← hA, mul_comm t]
  exact mul_le_mul_of_nonneg_left hts hdetA.le

end

end GroundTheory.Heights₂.Heights
