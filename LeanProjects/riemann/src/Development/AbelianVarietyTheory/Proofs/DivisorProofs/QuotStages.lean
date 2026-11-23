import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.QuotStage

open Matrix

theorem quotGram_eq_inv_toBlocks₂₂ {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (hH : IsUnit H.det)
    (hu : IsUnit (subGram H).det) : quotGram H = (H⁻¹.toBlocks₂₂)⁻¹ := by
  have hS : IsUnit (quotGram H).det := isUnit_det_quotGram hH hu
  letI iA : Invertible H.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  have hS' : IsUnit (H.toBlocks₂₂ - H.toBlocks₂₁ * ⅟H.toBlocks₁₁ * H.toBlocks₁₂).det := by
    rw [invOf_eq_nonsing_inv]; exact hS
  letI iS : Invertible (H.toBlocks₂₂ - H.toBlocks₂₁ * ⅟H.toBlocks₁₁ * H.toBlocks₁₂) :=
    invertibleOfIsUnitDet _ hS'
  letI iH : Invertible (fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂) :=
    fromBlocks₁₁Invertible _ _ _ _
  have h1 : H⁻¹ = ⅟(fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂) := by
    rw [invOf_eq_nonsing_inv, fromBlocks_toBlocks]
  rw [h1, invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₂₂, ← invOf_eq_nonsing_inv (⅟ _), invOf_invOf,
    quotGram, invOf_eq_nonsing_inv]

theorem quotStages : ∀ (m l n : Type) [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l] [DecidableEq n], (∀ K : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ, K.PosDef → subGram (quotGram K) = quotGram (K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) ∧ quotGram (quotGram K) = quotGram (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))) ∧ ∀ (m' l' : Type) [Fintype m'] [Fintype l'] [DecidableEq m'] (e : m' ≃ m) (f : l' → l) (K : Matrix (m ⊕ l) (m ⊕ l) ℂ), quotGram (K.submatrix (Sum.map e f) (Sum.map e f)) = (quotGram K).submatrix f f := by
  intro m l n _ _ _ _ _ _
  refine ⟨fun K hK => ⟨?_, ?_⟩, ?_⟩
  · have h11 : (K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).toBlocks₁₁ = K.toBlocks₁₁ := by
      ext; rfl
    rw [quotGram, quotGram, h11, subGram]
    ext i j
    simp only [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply, Matrix.sub_apply, mul_apply,
      submatrix_apply, Sum.map_inl, Sum.map_inr, id]
  · have hKu : IsUnit K.det := (isUnit_iff_isUnit_det _).1 hK.isUnit
    have hKs : IsUnit (subGram K).det := (isUnit_iff_isUnit_det _).1 (posDef_subGram hK).isUnit
    have hQ := posDef_quotGram hK
    have hQu : IsUnit (quotGram K).det := (isUnit_iff_isUnit_det _).1 hQ.isUnit
    have hQs : IsUnit (subGram (quotGram K)).det :=
      (isUnit_iff_isUnit_det _).1 (posDef_subGram hQ).isUnit
    have hB : (K⁻¹.toBlocks₂₂).PosDef := hK.inv.submatrix Sum.inr_injective
    have hBu : IsUnit (K⁻¹.toBlocks₂₂).det := (isUnit_iff_isUnit_det _).1 hB.isUnit
    have hQinv : (quotGram K)⁻¹ = K⁻¹.toBlocks₂₂ := by
      rw [quotGram_eq_inv_toBlocks₂₂ K hKu hKs, nonsing_inv_nonsing_inv _ hBu]
    have hK' := hK.submatrix (Equiv.sumAssoc m l n).injective
    have hK'u : IsUnit (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)).det :=
      (isUnit_iff_isUnit_det _).1 hK'.isUnit
    have hK's : IsUnit (subGram (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))).det :=
      (isUnit_iff_isUnit_det _).1 (posDef_subGram hK').isUnit
    rw [quotGram_eq_inv_toBlocks₂₂ _ hQu hQs, hQinv, quotGram_eq_inv_toBlocks₂₂ _ hK'u hK's,
      inv_submatrix_equiv]
    rfl
  · intro m' l' _ _ _ e f K
    have h11 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = K.toBlocks₁₁.submatrix e e := by
      ext; rfl
    have h12 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₂ = K.toBlocks₁₂.submatrix e f := by
      ext; rfl
    have h21 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = K.toBlocks₂₁.submatrix f e := by
      ext; rfl
    have h22 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₂ = K.toBlocks₂₂.submatrix f f := by
      ext; rfl
    rw [quotGram, quotGram, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv,
      submatrix_mul_equiv]
    rfl

end GlobalTheory.QuotStage
