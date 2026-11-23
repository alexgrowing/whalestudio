import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcNorm_norm_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hz
  have h3 : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [← h2]
  rw [h3, Complex.norm_real]
  simp only [Complex.ofReal_re, Real.norm_eq_abs]
  exact abs_of_pos (by simpa using h1)

theorem fcNorm_arith {ne nw ns h₁ h₂ t u : ℝ} (hh₂ : 0 < h₂) (ht : 0 < t)
    (hnw : nw * h₂ = t) (hmain : ne * ne * h₂ * h₁ = t * u * ns) :
    (ne / nw) ^ 2 * h₁ = u * t⁻¹ * ns * h₂ := by
  have hnw' : nw = t / h₂ := by field_simp; exact hnw
  have e : (ne / (t / h₂)) ^ 2 * h₁ = (ne * ne * h₂ * h₁) * h₂ / t ^ 2 := by
    field_simp
  rw [hnw', e, hmain]
  field_simp

theorem fcNorm : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  intro p q A A' S H₁ H₂ hH₁ hH₂ hS h
  have hd₁ : 0 < H₁.det := hH₁.det_pos
  have hd₂ : 0 < H₂.det := hH₂.det_pos
  have hn₁ := fcNorm_norm_of_pos hd₁
  have hn₂ := fcNorm_norm_of_pos hd₂
  have hr₂ : 0 < H₂.det.re := (Complex.lt_def.mp hd₂).1
  have hc : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hnc : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  have hAstar : (A.map star)ᵀ = Aᴴ := by ext i j; simp [conjTranspose_apply]
  have hB'H : (A'.map star)ᴴ = A'ᵀ := by ext i j; simp [conjTranspose_apply]
  have hT : Aᴴ * H₁ᵀ * A - A'ᵀ * H₂ * A'.map star = (2 * Complex.I) • Sᵀ := by
    have := congrArg Matrix.transpose h
    rw [transpose_sub, transpose_transpose, transpose_smul, transpose_mul, transpose_mul,
      transpose_transpose, hAstar, ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨B', hB'⟩ : ∃ B', B' = A'.map star := ⟨_, rfl⟩
  rw [← hB'] at hT hB'H
  obtain ⟨E, hE⟩ : ∃ E, E = fromRows B' A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = fromCols (-(A'ᵀ * H₂)) (Aᴴ * H₁ᵀ) := ⟨_, rfl⟩
  have hME : M * E = (2 * Complex.I) • Sᵀ := by
    rw [hM, hE, fromCols_mul_fromRows, ← hT, Matrix.neg_mul]
    abel
  have hMD : M = Eᴴ * fromBlocks (-H₂) 0 0 H₁ᵀ := by
    rw [hM, hE, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, hB'H]
    simp
  have hdetME : M.det * E.det = (2 * Complex.I) ^ (q + p) * S.det := by
    rw [← det_mul, hME, det_smul, det_transpose]
    simp
  have hne : (2 * Complex.I) ^ (q + p) * S.det ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hS
  have hMu : IsUnit M := (isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (hdetME ▸ hne)))
  have hEdet : E.det ≠ 0 := right_ne_zero_of_mul (hdetME ▸ hne)
  have hEu : IsUnit E := (isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEdet)
  have hmain : ‖E.det‖ * ‖E.det‖ * H₂.det.re * H₁.det.re
      = (2 : ℝ) ^ q * 2 ^ p * ‖S.det‖ := by
    have h1 := congrArg norm hdetME
    rw [hMD, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_neg, det_transpose] at h1
    simp only [norm_mul, norm_pow, hnc, norm_star, norm_neg, norm_one, one_pow, one_mul, hn₁, hn₂,
      Fintype.card_fin] at h1
    rw [pow_add] at h1
    linarith
  have hSu : IsUnit (Sᵀ).det := by
    rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hS
  have hSinv : Sᵀ * (Sᵀ)⁻¹ = 1 := mul_nonsing_inv _ hSu
  have hH₂u : IsUnit H₂.det := isUnit_iff_ne_zero.mpr hd₂.ne'
  have hH₂inv : H₂ * H₂⁻¹ = 1 := mul_nonsing_inv _ hH₂u
  have hH₂inv' : H₂⁻¹ * H₂ = 1 := nonsing_inv_mul _ hH₂u
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (Sᵀ)⁻¹ * A'ᵀ := ⟨_, rfl⟩
  rw [← hΦ]
  have hEΦ : E * Φ = fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have hMi : M⁻¹ * M = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hMu)
    have hkey : M * (E * Φ)
        = M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
      rw [← Matrix.mul_assoc, hME, hΦ, Matrix.smul_mul, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]
      rw [hM, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.mul_smul, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hH₂inv, Matrix.mul_one]
    calc E * Φ = M⁻¹ * (M * (E * Φ)) := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
      _ = M⁻¹ * (M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)) := by
        rw [hkey]
      _ = _ := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
  rw [hE, fromRows_mul] at hEΦ
  obtain ⟨hBΦ, hAΦ⟩ := fromRows_inj hEΦ
  have hrA : A.rank = p := by
    obtain ⟨X, hXd⟩ : ∃ X, X = E⁻¹ * fromRows (0 : Matrix (Fin q) (Fin p) ℂ)
        (1 : Matrix (Fin p) (Fin p) ℂ) := ⟨_, rfl⟩
    have hX : E * X = fromRows 0 1 := by
      rw [hXd, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hEdet), Matrix.one_mul]
    rw [hE, fromRows_mul] at hX
    obtain ⟨-, hX2⟩ := fromRows_inj hX
    have h1 := rank_mul_le_left A X
    rw [hX2, rank_one, Fintype.card_fin] at h1
    have h2 := rank_le_card_height A
    rw [Fintype.card_fin] at h2
    omega
  have hw : (B' * Φ).det * H₂.det = (-(2 * Complex.I)) ^ q := by
    have e : (2 * Complex.I) • (-1 : Matrix (Fin q) (Fin q) ℂ) = (-(2 * Complex.I)) • 1 := by simp
    rw [← det_mul, hBΦ, Matrix.smul_mul, Matrix.neg_mul, hH₂inv', e, det_smul, det_one,
      Fintype.card_fin, mul_one]
  have hwne : (B' * Φ).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact pow_ne_zero _ (neg_ne_zero.mpr hc) hw.symm
  have hrΦ : Φ.rank = q := by
    have h1 := rank_mul_le_right B' Φ
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hwne)),
      Fintype.card_fin] at h1
    have h2 := rank_le_card_width Φ
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨hy, -, hN⟩ := fcIndep p q A Φ hAΦ hrA hrΦ
  have hN' := hN B'
  rw [← hE] at hN'
  refine ⟨hAΦ, hrA, hrΦ, ?_⟩
  have hq : (fromRows Φᴴ A).det / (Φᴴ * Φ).det = E.det / (B' * Φ).det := by
    field_simp
    linear_combination -hN'
  have hnw : ‖(B' * Φ).det‖ * H₂.det.re = (2 : ℝ) ^ q := by
    have := congrArg norm hw
    simpa [hn₂, hnc] using this
  rw [hq, norm_div, inv_pow]
  have hfin := fcNorm_arith (ne := ‖E.det‖) (ns := ‖S.det‖) (h₁ := H₁.det.re) (u := (2:ℝ)^p) hr₂
    (by positivity) hnw hmain
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Flat
