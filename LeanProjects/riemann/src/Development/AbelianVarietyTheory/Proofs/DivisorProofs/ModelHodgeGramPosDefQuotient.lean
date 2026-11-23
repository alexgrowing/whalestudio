import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

namespace GlobalTheory.ModelHodgeBlocks

theorem conjTranspose_transpose_eq_map {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    Zᴴᵀ = Z.map (starRingEnd ℂ) := by
  ext i j; simp [conjTranspose_apply]

theorem modelHodgeGram_eq_fromBlocks {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    modelHodgeGram Z = fromBlocks (-1 + Zᵀ * Z.map (starRingEnd ℂ)) Zᵀ (Z.map (starRingEnd ℂ)) 1 := by
  simp [modelHodgeGram, modelFrame, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply,
    conjTranspose_transpose_eq_map]

theorem push_expand {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℂ) (Y : Matrix (Fin q) (Fin p) ℂ)
    (N : Matrix (Fin q) (Fin q) ℂ) :
    (1 - X * Y) * (1 + X * N * Y) = 1 + X * ((1 - Y * X) * N - 1) * Y := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

theorem push_expand' {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℂ) (Y : Matrix (Fin q) (Fin p) ℂ)
    (N : Matrix (Fin q) (Fin q) ℂ) :
    (1 + X * N * Y) * (1 - X * Y) = 1 + X * (N * (1 - Y * X) - 1) * Y := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

theorem posDef_one_sub_mul_conjTranspose {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ)
    (h : (1 - Zᴴ * Z).PosDef) : (1 - Z * Zᴴ).PosDef := by
  have hu : IsUnit (1 - Zᴴ * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have hP : (1 + Z * (1 - Zᴴ * Z)⁻¹ * Zᴴ).PosDef := by
    have := h.inv.posSemidef.conjTranspose_mul_mul_same Zᴴ
    rw [conjTranspose_conjTranspose] at this
    exact Matrix.PosDef.one.add_posSemidef this
  have hinv : (1 + Z * (1 - Zᴴ * Z)⁻¹ * Zᴴ)⁻¹ = 1 - Z * Zᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [push_expand', Matrix.nonsing_inv_mul _ hu]
    simp
  rw [← hinv]
  exact hP.inv

end GlobalTheory.ModelHodgeBlocks

open GlobalTheory.ModelHodgeBlocks in

theorem GlobalTheory.modelHodgeGram_blocks : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ), (1 - Zᴴ * Z).PosDef →
    (1 - Z.map (starRingEnd ℂ) * Zᵀ).PosDef ∧ (1 - Zᵀ * Z.map (starRingEnd ℂ)).PosDef ∧
    GlobalTheory.HermFrame.quotGram (modelHodgeGram Z) = (1 - Z.map (starRingEnd ℂ) * Zᵀ)⁻¹ ∧
    -GlobalTheory.HermFrame.subGram (modelHodgeGram Z) = 1 - Zᵀ * Z.map (starRingEnd ℂ) := by
  intro p q Z h
  have e1 : 1 - Z.map (starRingEnd ℂ) * Zᵀ = (1 - Z * Zᴴ)ᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul, conjTranspose_transpose_eq_map]
  have e2 : 1 - Zᵀ * Z.map (starRingEnd ℂ) = (1 - Zᴴ * Z)ᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul, conjTranspose_transpose_eq_map]
  have h2 : (1 - Zᵀ * Z.map (starRingEnd ℂ)).PosDef := by rw [e2]; exact h.transpose
  have hu : IsUnit (1 - Zᵀ * Z.map (starRingEnd ℂ)) := h2.isUnit
  have hu' : IsUnit (-1 + Zᵀ * Z.map (starRingEnd ℂ)).det := by
    have : -1 + Zᵀ * Z.map (starRingEnd ℂ) = -(1 - Zᵀ * Z.map (starRingEnd ℂ)) := by abel
    rw [this]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu.neg
  refine ⟨?_, h2, ?_, ?_⟩
  · rw [e1]; exact (posDef_one_sub_mul_conjTranspose Z h).transpose
  · rw [modelHodgeGram_eq_fromBlocks]
    simp only [GlobalTheory.HermFrame.quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂]
    symm
    apply Matrix.inv_eq_right_inv
    have key : 1 - Z.map (starRingEnd ℂ) * (-1 + Zᵀ * Z.map (starRingEnd ℂ))⁻¹ * Zᵀ =
        1 + Z.map (starRingEnd ℂ) * (-(-1 + Zᵀ * Z.map (starRingEnd ℂ))⁻¹) * Zᵀ := by
      simp [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
    rw [key, push_expand]
    have : (1 - Zᵀ * Z.map (starRingEnd ℂ)) * -(-1 + Zᵀ * Z.map (starRingEnd ℂ))⁻¹ = 1 := by
      have h0 : 1 - Zᵀ * Z.map (starRingEnd ℂ) = -(-1 + Zᵀ * Z.map (starRingEnd ℂ)) := by abel
      rw [h0, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_nonsing_inv _ hu']
    rw [this]; simp
  · rw [modelHodgeGram_eq_fromBlocks]
    simp only [GlobalTheory.HermFrame.subGram, toBlocks_fromBlocks₁₁]
    abel
