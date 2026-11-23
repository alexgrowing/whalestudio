import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

variable {m n : Type*} [Fintype m] [Fintype n]

theorem posDef_fromBlocks_diag {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end KCoord

variable {g : ℕ}

namespace KCoord

def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1

noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y

theorem siegelGram_eq (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]

theorem unip_mem (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]

theorem diagInv_mem (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]

theorem unip_isUnit (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]

theorem siegelGram_mem_posDef (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end KCoord

namespace KCoord

theorem existsUnique_siegelGram (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by
  have hGt : Gᵀ = G := by
    have := hG.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hS' := hS
  rw [SymplecticGroup.mem_iff, hGt] at hS'
  have hGb := Matrix.fromBlocks_toBlocks G
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGt' := hGt
  rw [← hGb] at hS' hGt'
  simp only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hS'
  obtain ⟨t1, -, t3, -⟩ := Matrix.fromBlocks_inj.mp hGt'
  simp at e1 e2
  have hBA : B * A = A * C := by
    have := e1
    rwa [add_neg_eq_zero] at this
  have hAD : A * D = 1 + B * B := by
    have h1 : A * D = B * B - (B * B + -(A * D)) := by abel
    rw [h1, e2]; abel
  have hA : A.PosDef := hG.submatrix Sum.inl_injective
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, t1]
  have hCt : Bᵀ = C := t3
  have k : A⁻¹ * B = C * A⁻¹ := by
    calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAAi, Matrix.mul_one]
      _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * C) * A⁻¹ := by rw [hBA]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A C, hAiA, Matrix.one_mul]
  have hX : (A⁻¹ * B).IsSymm := by
    show (A⁻¹ * B)ᵀ = A⁻¹ * B
    rw [Matrix.transpose_mul, hAit, hCt, k]
  have hY : (A⁻¹).PosDef := hA.inv
  have hYinv : (A⁻¹)⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAdet
  refine ⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩
  · show G = siegelGram (A⁻¹ * B) A⁻¹
    rw [siegelGram, hYinv]
    conv_lhs => rw [← hGb]
    congr 1
    · rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [k, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · have hD : D = A⁻¹ * (1 + B * B) := by
        rw [← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      rw [hD, k, Matrix.mul_add, Matrix.mul_one]
      congr 1
      calc A⁻¹ * (B * B) = A⁻¹ * B * (A * A⁻¹) * B := by
            rw [hAAi, Matrix.mul_one, Matrix.mul_assoc]
        _ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]
  · rintro ⟨X', Y'⟩ ⟨hX', hY', hG'⟩
    have hY'det : IsUnit Y'.det := (Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit
    have h11 : A = Y'⁻¹ := by
      rw [hAdef, hG']; simp [siegelGram]
    have h12 : B = Y'⁻¹ * X' := by
      rw [hBdef, hG']; simp [siegelGram]
    have hYY : Y' = A⁻¹ := by
      rw [h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]
    have hXX : X' = A⁻¹ * B := by
      rw [h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]
    simp only [Prod.mk.injEq]
    exact ⟨hXX, hYY⟩

end KCoord

theorem SiegelCoordinates.intersectionNumber_baseChange : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩

end GroundTheory.Heights₂.Heights
