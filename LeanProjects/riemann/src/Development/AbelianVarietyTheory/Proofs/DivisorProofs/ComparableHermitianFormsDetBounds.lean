import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec

open Matrix
open scoped ComplexOrder Matrix MatrixOrder

namespace GlobalTheory.CompMetric

theorem inv_sub_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {c : ℝ} (hc : 0 < c)
    (hA : A.PosDef) (hB : B.PosDef) (h : (((c : ℂ) • B) - A).PosSemidef) :
    (((c : ℂ) • A⁻¹) - B⁻¹).PosSemidef := by
  have h' : A ≤ c • B := by
    rw [Matrix.le_iff, RCLike.real_smul_eq_coe_smul (K := ℂ)]; exact h
  have h1 := GlobalTheory.inv_le_inv_of_posDef_of_le hA h'
  rw [GlobalTheory.inv_real_smul_of_posDef hB hc.ne'] at h1
  have h2 := (Matrix.le_iff.mp h1).smul hc.le
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] at h2
  exact h2

theorem det_re_le_of_sub {n k : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hA : A.PosDef) (h : (((c : ℂ) • B) - A).PosSemidef) (P : Matrix (Fin n) (Fin k) ℂ) :
    (P.conjTranspose * A * P).det.re ≤ c ^ k * (P.conjTranspose * B * P).det.re := by
  have h' : A ≤ c • B := by
    rw [Matrix.le_iff, RCLike.real_smul_eq_coe_smul (K := ℂ)]; exact h
  have h1 := GlobalTheory.conjTranspose_mul_mul_le_of_le h' P
  have h2 := GlobalTheory.re_det_le_re_det_of_posSemidef_of_le
    (hA.posSemidef.conjTranspose_mul_mul_same P) h1
  rw [Matrix.mul_smul, Matrix.smul_mul, RCLike.real_smul_eq_coe_smul (K := ℂ), det_smul,
    Fintype.card_fin] at h2
  simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using h2

theorem comparable_metrics : ∀ (n : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (m : ℝ), 1 ≤ m → G.PosDef → G₀.PosDef → (((m : ℂ) • G₀) - G).PosSemidef → (((m : ℂ) • G) - G₀).PosSemidef → (((m : ℂ) • G₀⁻¹) - G⁻¹).PosSemidef ∧ (((m : ℂ) • G⁻¹) - G₀⁻¹).PosSemidef ∧ ∀ (k : ℕ) (P : Matrix (Fin n) (Fin k) ℂ), (P.conjTranspose * G * P).det.re ≤ m ^ k * (P.conjTranspose * G₀ * P).det.re ∧ (P.conjTranspose * G₀ * P).det.re ≤ m ^ k * (P.conjTranspose * G * P).det.re := by
  intro n G G₀ m hm hG hG₀ h1 h2
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  exact ⟨inv_sub_posSemidef hm0 hG₀ hG h2, inv_sub_posSemidef hm0 hG hG₀ h1,
    fun k P => ⟨det_re_le_of_sub hm0.le hG h1 P, det_re_le_of_sub hm0.le hG₀ h2 P⟩⟩

end GlobalTheory.CompMetric
