import Mathlib

theorem UpperTheory.Reformulated.B.ExistsColumnVector.ex_col :
    ∀ {k : Type} [inst : Field k] {n : ℕ} (v : Fin (n + (1 : ℕ)) → k),
    v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
      ∃ (q : GL (Fin (n + (1 : ℕ))) k),
        (↑q : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec (Pi.single (0 : Fin (n + (1 : ℕ))) (1 : k)) =
          v := by
  intro k _ n v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  have h1 : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have h2 : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i v).submatrix id
      (Equiv.swap 0 i)).det ≠ 0 := by
    rw [Matrix.det_permute', h1]
    refine mul_ne_zero ?_ hi'
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 i)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h2, ?_⟩
  ext j
  simp [Matrix.mulVec_single_one, Matrix.GeneralLinearGroup.mkOfDetNeZero]
