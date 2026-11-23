import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContinuousWeightFactorUnitary

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

def mob (M : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (M.toBlocks₁₁ * Z + M.toBlocks₁₂) * (M.toBlocks₂₁ * Z + M.toBlocks₂₂)⁻¹

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem mob_mul (M N : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) (hV : IsUnit (N.toBlocks₂₁ * Z + N.toBlocks₂₂).det) :
    mob (M * N) Z = mob M (mob N Z) := by
  set V := N.toBlocks₂₁ * Z + N.toBlocks₂₂ with hVdef
  set W := N.toBlocks₁₁ * Z + N.toBlocks₁₂ with hWdef
  have h1 : (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = M.toBlocks₁₁ * W + M.toBlocks₁₂ * V := by
    rw [toBlocks₁₁_mul, toBlocks₁₂_mul, hVdef, hWdef]; noncomm_ring
  have h2 : (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = M.toBlocks₂₁ * W + M.toBlocks₂₂ * V := by
    rw [toBlocks₂₁_mul, toBlocks₂₂_mul, hVdef, hWdef]; noncomm_ring
  clear_value V W
  have hVV : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV
  have hVV' : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hV
  have e1 : M.toBlocks₁₁ * (W * V⁻¹) + M.toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have e2 : M.toBlocks₂₁ * (W * V⁻¹) + M.toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  unfold mob
  rw [h1, h2, ← hWdef, ← hVdef, e1, e2, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv V hV, Matrix.mul_assoc,
    ← Matrix.mul_assoc V⁻¹, hVV', Matrix.one_mul]

theorem mob_nU (b Z : Matrix (Fin n) (Fin n) ℂ) : mob (nU b) Z = Z + b := by
  simp [mob, nU]

theorem mob_mLc (a Z : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : mob (mLc a) Z = a * Z * aᴴ := by
  have h : IsUnit (aᴴ).det := by rw [Matrix.det_conjTranspose]; exact ha.star
  simp [mob, mLc, Matrix.nonsing_inv_nonsing_inv _ h]

theorem mob_JJ_diag (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    mob (JJ n) (Matrix.diagonal z) = Matrix.diagonal fun j => (-z j)⁻¹ := by
  simp only [mob, JJ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul, Matrix.neg_mul]
  rw [Matrix.diagonal_neg]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hz i]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

abbrev Z0 (sg : ℤˣ) : Matrix (Fin n) (Fin n) ℂ := (Complex.I * ((sg : ℤ) : ℂ)) • 1

theorem sg_sq (sg : ℤˣ) : ((sg : ℤ) : ℂ) * ((sg : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or sg with h | h <;> simp [h]

theorem mob_K (sg : ℤˣ) (M : M2 n) (hM : InK M) (hV : IsUnit (M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂).det) :
    mob M (Z0 sg) = Z0 sg := by
  obtain ⟨hG, hU⟩ := hM
  have hU' : M * Mᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * M = M * JJ n := by
    calc JJ n * M = (M * Mᴴ) * JJ n * M := by rw [hU', Matrix.one_mul]
      _ = M * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = M * JJ n := by rw [hG]
  have hM' := Matrix.fromBlocks_toBlocks M
  rw [← hM'] at hc
  simp only [JJ, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero] at hc
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hc
  set σ : ℂ := ((sg : ℤ) : ℂ)
  have hσ := sg_sq sg
  set X := M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂ with hX
  have hnum : M.toBlocks₁₁ * Z0 sg + M.toBlocks₁₂ = (Complex.I * σ) • X := by
    rw [hX, e1, e2]
    simp only [Z0, Matrix.mul_smul, Matrix.mul_one, smul_add, Matrix.neg_mul, smul_neg, smul_smul]
    rw [show Complex.I * σ * (Complex.I * σ) = -1 by rw [mul_mul_mul_comm, Complex.I_mul_I, hσ]; ring]
    simp [neg_smul]; abel
  unfold mob
  rw [hnum, ← hX, Matrix.smul_mul, Matrix.mul_nonsing_inv X hV]

end PositivityTheory.SiegelWeilFormula.KLI

end
