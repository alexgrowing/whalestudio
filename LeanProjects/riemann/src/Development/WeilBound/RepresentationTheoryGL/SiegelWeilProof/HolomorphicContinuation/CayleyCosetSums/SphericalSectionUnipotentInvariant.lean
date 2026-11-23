import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolTBase
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem upper_left_block_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem upper_right_block_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem det_mR_ne (y : GR n) : (mR y).det ≠ 0 := by
  have h : IsUnit (mR y) := (y.1).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem isUnit_first_cayley_block (y : GR n) : IsUnit (u1 (mR y)) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (detU1 n y).1)

theorem spherical_section_ne_zero_group (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y ≠ 0 := by
  have h1 := det_mR_ne y
  obtain ⟨h2, h3⟩ := detU1 n y
  simp only [F0, f0]
  exact mul_ne_zero (zpow_ne_zero _ h1) (mul_ne_zero (zpow_ne_zero _ h2) (zpow_ne_zero _ h3))

theorem zOf_nU' (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) : zOf (x * y) = zOf y + h := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hU := isUnit_first_cayley_block y
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [nU, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.one_mul]
  have key : (Complex.I • ((mR y).toBlocks₁₁ + h * (mR y).toBlocks₂₁) + ((mR y).toBlocks₁₂ + h * (mR y).toBlocks₂₂)) =
      (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂) + h * u1 (mR y) := by
    simp only [u1, Matrix.mul_add, Matrix.mul_smul, smul_add]
    abel
  rw [key, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.mul_one]

theorem spherical_section_unipotent_invariant (p q : ℕ) (e : ℤ) (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) :
    F0 p q e (x * y) = F0 p q e y := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hu2 : u2 (mR (x * y)) = u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hd : (mR (x * y)).det = (mR y).det := by
    rw [hm, Matrix.det_mul, nU, Matrix.det_fromBlocks_zero₂₁]
    simp
  simp only [F0, f0, hu1, hu2, hd]

theorem levi_inv (a a' : Matrix (Fin n) (Fin n) ℂ) (x : GR n) (hx : mR x = fromBlocks a 0 0 a') : aᴴ * a' = 1 := by
  obtain ⟨-, E2, -⟩ := IwaPf.inG_blocks (mR x) x.2
  rw [hx] at E2
  simpa using E2

theorem zOf_levi' (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    zOf (x * y) = a * zOf y * aᴴ := by
  have hinv := levi_inv a a' x hx
  have ha' : a'⁻¹ = aᴴ := Matrix.inv_eq_left_inv hinv
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.zero_mul, add_zero]
  rw [Matrix.mul_inv_rev, ha']
  simp only [← Matrix.mul_smul, ← Matrix.mul_add, Matrix.mul_assoc]

theorem spherical_section_levi_mul (p q : ℕ) (e : ℤ) (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    F0 p q e (x * y) = F0 p q e x * F0 p q e y := by
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  have hu2 : u2 (mR (x * y)) = a' * u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have hx1 : u1 (mR x) = a' := by simp [u1, hx]
  have hx2 : u2 (mR x) = a' := by simp [u2, hx]
  have hd : (mR (x * y)).det = (mR x).det * (mR y).det := by rw [mR_mul, Matrix.det_mul]
  simp only [F0, f0, hu1, hu2, hx1, hx2, hd, Matrix.det_mul, mul_zpow]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
