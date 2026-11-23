import Mathlib

namespace GlobalTheory.DiagonalConjugateExistence

theorem exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hA, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]
  have hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  ext i j
  have := congrFun (hv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

end GlobalTheory.DiagonalConjugateExistence
