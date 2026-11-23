import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InnerGen
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def v1 (b : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • b.toBlocks₁₁ + b.toBlocks₁₂

theorem fz_zero (e : ℤ) (x : M2 n) : fz m e 0 x = x.det ^ e * (u1 x).det ^ (-(m : ℤ)) := by
  simp [fz]

theorem blocks_mul (g b : M2 n) : (g * b).toBlocks₂₁ = g.toBlocks₂₁ * b.toBlocks₁₁ + g.toBlocks₂₂ * b.toBlocks₂₁ ∧
    (g * b).toBlocks₂₂ = g.toBlocks₂₁ * b.toBlocks₁₂ + g.toBlocks₂₂ * b.toBlocks₂₂ := by
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.add_apply]

theorem second_coord_mul_inner (g b : M2 n) : u1 (g * b) = g.toBlocks₂₁ * v1 b + g.toBlocks₂₂ * u1 b := by
  obtain ⟨h1, h2⟩ := blocks_mul g b
  simp only [u1, v1, h1, h2, Matrix.mul_add, Matrix.mul_smul, smul_add]
  abel

theorem nU_blocks (y : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) :
    (y * nU S).toBlocks₂₁ = y.toBlocks₂₁ ∧ (y * nU S).toBlocks₂₂ = y.toBlocks₂₁ * S + y.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := blocks_mul y (nU S)
  simp only [nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem det_nU (S : Matrix (Fin n) (Fin n) ℂ) : (nU S).det = 1 := by
  simp [nU]

private theorem mul_JJ_mul_conjTranspose_eq_of_inG (y : M2 n) (hy : InG y) : y * JJ n * yᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := by
    ext (i|i) (j|j) <;> simp [JJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hy' : yᴴ * JJ n * y = JJ n := hy
  have h1 : (-(JJ n * yᴴ * JJ n)) * y = 1 := by
    calc (-(JJ n * yᴴ * JJ n)) * y = -(JJ n * (yᴴ * JJ n * y)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJ, neg_neg]
  have h2 : y * (-(JJ n * yᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc y * JJ n * yᴴ = y * JJ n * yᴴ * (-(JJ n * JJ n)) := by rw [hJ, neg_neg, Matrix.mul_one]
    _ = (y * (-(JJ n * yᴴ * JJ n))) * JJ n := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [h2, Matrix.one_mul]

theorem hermit_cd (y : M2 n) (hy : InG y) (hc : IsUnit y.toBlocks₂₁.det) :
    (y.toBlocks₂₁⁻¹ * y.toBlocks₂₂).IsHermitian := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_mul_conjTranspose_eq_of_inG y hy)
  rw [← Matrix.fromBlocks_toBlocks y] at h
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at h
  rw [neg_add_eq_zero] at h
  have hcH : IsUnit (y.toBlocks₂₁)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hc
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc (y.toBlocks₂₂)ᴴ * (y.toBlocks₂₁)ᴴ⁻¹
      = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₁ * (y.toBlocks₂₂)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
    _ = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₂ * (y.toBlocks₂₁)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by rw [← h]
    _ = (y.toBlocks₂₁)⁻¹ * y.toBlocks₂₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcH, Matrix.mul_one]

theorem v_rel (b : M2 n) (hb : InG b) : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e := hb
  unfold InG at e
  rw [← Matrix.fromBlocks_toBlocks b] at e
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  have key : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b =
      -(-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₁)
      - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₂)
      + Complex.I • ((-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₂)
        - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₁)) := by
    simp only [u1, v1, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]
    match_scalars <;>
      first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
  rw [key, e1, e2, e3, e4]
  module

end PositivityTheory.Rg.Sw.HSt.L3
