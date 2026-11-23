import Mathlib

namespace UpperTheory.Reformulated.B.MirabolicColumnBlock

theorem conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d := by
  have hev : ∀ a, ∃ v : Fin n → K, Module.End.HasEigenvector (Matrix.toLin' M) (d a) v := by
    intro a
    apply Module.End.HasEigenvalue.exists_hasEigenvector
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using hev
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  have hu : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hmul : M * (Matrix.of v).transpose = (Matrix.of v).transpose * Matrix.diagonal d := by
    ext i a
    have h := congrFun (hv a).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hmul, ← hu, ← Matrix.mul_assoc]
  simp

end UpperTheory.Reformulated.B.MirabolicColumnBlock
