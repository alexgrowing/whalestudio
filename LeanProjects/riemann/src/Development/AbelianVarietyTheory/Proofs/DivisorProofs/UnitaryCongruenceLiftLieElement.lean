import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing

open Matrix

namespace GlobalTheory.CayleyUnit

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_mul'' (τ : R →+* R) (A B : Matrix n n R) :
    Formalism.UG.cT τ (A * B) = Formalism.UG.cT τ B * Formalism.UG.cT τ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one'' (τ : R →+* R) : Formalism.UG.cT τ (1 : Matrix n n R) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_add'' (τ : R →+* R) (A B : Matrix n n R) :
    Formalism.UG.cT τ (A + B) = Formalism.UG.cT τ A + Formalism.UG.cT τ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub'' (τ : R →+* R) (A B : Matrix n n R) :
    Formalism.UG.cT τ (A - B) = Formalism.UG.cT τ A - Formalism.UG.cT τ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul'' (τ : R →+* R) (c : R) (A : Matrix n n R) :
    Formalism.UG.cT τ (c • A) = τ c • Formalism.UG.cT τ A := by
  ext i j; simp [Formalism.UG.cT]

theorem cayley_unit : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R)
    (H X : Matrix n n R) (p w : R) (k : ℕ), (∀ a, τ (τ a) = a) → τ p = p → w + τ w = 1 →
    (∀ s, IsUnit (1 + p * s)) → 1 ≤ k → Formalism.UG.cT τ X * H + H * X = 0 →
    ∃ g X' D : Matrix n n R, Formalism.UG.cT τ g * H * g = H ∧ g = 1 + p ^ k • X' ∧ X' = X + p • D := by
  intro R _ n _ _ τ H X p w k hτ hp hw hu hk hX
  set Z : Matrix n n R := p ^ k • X with hZ
  set B : Matrix n n R := 1 + w • Z with hB
  set C : Matrix n n R := 1 - τ w • Z with hC

  have hdet : IsUnit C.det := by
    let f := Ideal.Quotient.mk (Ideal.span {p})
    have hf : C.map f = 1 := by
      have hp0 : f p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
      ext i j
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [hC, hZ, Matrix.map_apply, Matrix.one_apply, hp0, pow_succ]
    have h1 : f C.det = f 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hf, Matrix.det_one, map_one]
    rw [Ideal.Quotient.eq] at h1
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h1
    have : C.det = 1 + p * s := by rw [mul_comm, hs]; ring
    rw [this]; exact hu s
  have hCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
  have hCi' : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hdet
  have hXs : Formalism.UG.cT τ X * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  have hZs : Formalism.UG.cT τ Z * H = -(H * Z) := by
    rw [hZ, cT_smul'', map_pow, hp, Matrix.smul_mul, hXs, Matrix.mul_smul, smul_neg]
  have hBH : Formalism.UG.cT τ B * H = H * C := by
    rw [hB, hC, cT_add'', cT_one'', cT_smul'', Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hZs,
      Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, smul_neg, sub_eq_add_neg, hZ, Matrix.mul_smul,
      Matrix.mul_smul]
  have hCH : Formalism.UG.cT τ C * H = H * B := by
    rw [hB, hC, cT_sub'', cT_one'', cT_smul'', hτ, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hZs,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_neg, sub_neg_eq_add, hZ, Matrix.mul_smul,
      Matrix.mul_smul]
  have hcomm : B * C = C * B := by
    have hc : Commute (w • Z) (τ w • Z) := ((Commute.refl Z).smul_left w).smul_right (τ w)
    have : Commute B C :=
      (Commute.one_left C).add_left ((Commute.one_right (w • Z)).sub_right hc)
    exact this.eq
  refine ⟨B * C⁻¹, X * C⁻¹, p ^ (k - 1) • (τ w • (X * C⁻¹ * X)), ?_, ?_, ?_⟩
  · rw [cT_mul'', Matrix.mul_assoc (Formalism.UG.cT τ C⁻¹), hBH, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc C B, ← hcomm, Matrix.mul_assoc B, hCi, Matrix.mul_one,
      ← hCH, ← Matrix.mul_assoc, ← cT_mul'', hCi, cT_one'', Matrix.one_mul]
  · have hBC : B = C + Z := by
      have e : w • Z = Z - τ w • Z := by rw [eq_sub_iff_add_eq, ← add_smul, hw, one_smul]
      rw [hB, hC, e]; abel
    rw [hBC, Matrix.add_mul, hCi, hZ, Matrix.smul_mul]
  · have h1 : C⁻¹ = 1 + C⁻¹ * (τ w • Z) := by
      have : C⁻¹ * C = C⁻¹ - C⁻¹ * (τ w • Z) := by rw [hC, Matrix.mul_sub, Matrix.mul_one]
      rw [hCi'] at this
      rw [this]; abel
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    conv_lhs => rw [h1]
    rw [Matrix.mul_add, Matrix.mul_one, hZ, Nat.add_sub_cancel, smul_smul, Matrix.mul_smul, Matrix.mul_smul,
      smul_smul, ← Matrix.mul_assoc, smul_smul, pow_succ]
    congr 1
    rw [show τ w * (p ^ k' * p) = p * p ^ k' * τ w by ring]

end GlobalTheory.CayleyUnit
