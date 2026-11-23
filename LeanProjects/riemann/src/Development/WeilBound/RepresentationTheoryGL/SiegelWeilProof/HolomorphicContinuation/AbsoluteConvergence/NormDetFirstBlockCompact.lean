import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem projected_block_lower_sum (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem lowerDiagonalBlockAsGL (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := by
  simp [mR]

theorem k_blocks {k : GR n} (hk : k ∈ KR n) :
    (mR k).toBlocks₂₁ = -(mR k).toBlocks₁₂ ∧ (mR k).toBlocks₂₂ = (mR k).toBlocks₁₁ := by
  have hK : InK (mR k) := hk
  have h2 : mR k * (mR k)ᴴ = 1 := mul_eq_one_comm.1 hK.2
  have h3 : JJ n * mR k = mR k * JJ n := by
    calc JJ n * mR k = (mR k * (mR k)ᴴ) * (JJ n * mR k) := by rw [h2, Matrix.one_mul]
      _ = mR k * ((mR k)ᴴ * JJ n * mR k) := by simp only [Matrix.mul_assoc]
      _ = mR k * JJ n := by rw [hK.1]
  rw [← fromBlocks_toBlocks (mR k)] at h3
  unfold JJ at h3
  rw [fromBlocks_multiply, fromBlocks_multiply] at h3
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, fromBlocks_inj] at h3
  obtain ⟨h11, h12, _, _⟩ := h3
  exact ⟨h11, h12⟩

theorem first_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u1 (g * mR k) = u1 g * u1 (mR k) := by
  obtain ⟨hC, hD⟩ := k_blocks hk
  simp only [u1, projected_block_lower_sum, lowerDiagonalBlockAsGL, hC, hD]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    Matrix.mul_neg, smul_add, smul_neg, neg_smul, one_smul]
  abel

theorem second_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u2 (g * mR k) = u2 g * u2 (mR k) := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, h21, h22]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_add]
  abel

theorem first_block_compact_unitary {k : GR n} (hk : k ∈ KR n) : (u1 (mR k))ᴴ * u1 (mR k) = 1 := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  have hK : InK (mR k) := hk
  have e := hK.2
  rw [← fromBlocks_toBlocks (mR k), h21, h22, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at e
  obtain ⟨e11, e12, _, _⟩ := e
  unfold u1
  rw [h21, h22]
  simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at e11 e12
  simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_neg, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, neg_mul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
  rw [(add_neg_eq_zero.1 e12).symm, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, ← e11]
  abel

theorem norm_det_first_block_compact {k : GR n} (hk : k ∈ KR n) : ‖(u1 (mR k)).det‖ = 1 := by
  have h := congrArg Matrix.det (first_block_compact_unitary hk)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have h2 : Complex.normSq (u1 (mR k)).det = 1 := by
    have : ((Complex.normSq (u1 (mR k)).det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using h
    exact_mod_cast this
  have h3 : ‖(u1 (mR k)).det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h2
  have h4 : 0 ≤ ‖(u1 (mR k)).det‖ := norm_nonneg _
  nlinarith [h3, h4]

theorem first_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u1 (mR y * g) = (mR y).toBlocks₂₂ * u1 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul]

theorem second_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u2 (mR y * g) = (mR y).toBlocks₂₂ * u2 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem first_block_of_upper (y : GR n) (hy : IsUp y) : u1 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [hy']
  simp

theorem second_block_of_upper (y : GR n) (hy : IsUp y) : u2 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [hy']
  simp

theorem mult : Mult := by
  intro n p q e
  constructor
  · intro g k hk
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_mul_compact _ hk, second_block_mul_compact _ hk, det_mul, det_mul, det_mul, mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_mul_compact _ hk, det_mul, norm_mul, norm_det_first_block_compact hk, mul_one]
  · intro y g hy
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_upper_mul y _ hy, second_block_upper_mul y _ hy, first_block_of_upper y hy, second_block_of_upper y hy, det_mul, det_mul, det_mul,
        mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_upper_mul y _ hy, first_block_of_upper y hy, det_mul, norm_mul, mul_pow, mul_inv]

end PositivityTheory.Rg.Sw.AbsSt
