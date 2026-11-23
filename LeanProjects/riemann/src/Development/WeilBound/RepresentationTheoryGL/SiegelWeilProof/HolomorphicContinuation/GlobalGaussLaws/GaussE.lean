import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussD

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_conj (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    (actZ y Z)ᴴ = ((mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂)⁻¹ := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hM' := det_CZhD hg hZ
  have hid := identG hg Z Zᴴ
  rw [sub_self] at hid
  have hE := sub_eq_zero.mp hid
  unfold actZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  set N' := (mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂
  set M' := (mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂
  have hMh : IsUnit (Mᴴ).det := by
    rw [det_conjTranspose]
    exact hM.star
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  calc (Mᴴ)⁻¹ * Nᴴ = (Mᴴ)⁻¹ * (Nᴴ * M') * M'⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hM', Matrix.mul_one]
    _ = (Mᴴ)⁻¹ * (Mᴴ * N') * M'⁻¹ := by rw [hE]
    _ = N' * M'⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hMh, Matrix.one_mul]

theorem isSiegel_actZ (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) : IsSiegel (actZ y Z) := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hid := identG hg Z Z
  unfold IsSiegel actZ
  unfold IsSiegel at hZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
  have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
    rw [← neg_sub, hid, neg_sub]
  have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
      (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
    rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
  rw [key]
  refine Matrix.PosDef.conjTranspose_mul_mul_same hZ ?_
  exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hM))

end PositivityTheory.Rg.Sw.Glob.GaussH
