import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

namespace GlobalTheory.TruncationIsometry

open Matrix

theorem cT_cut {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε)
    (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
      ε • Formalism.UG.cT σ M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hσ]
  · have h' : j ≠ i := fun e => h e.symm
    simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne h']

theorem cut_isometry {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε) (hε : ε * ε = ε)
    (J M : Matrix (Fin n) (Fin n) R) (hM : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J *
      (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) = J := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, mul_one, h2, sub_zero]
  rw [cT_cut σ ε hσ M]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, hM, hε, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.TruncationIsometry
