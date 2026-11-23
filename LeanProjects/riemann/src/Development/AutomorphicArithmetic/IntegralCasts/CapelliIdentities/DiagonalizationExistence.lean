import Mathlib

theorem UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag :
    ∀ {κ : Type} [inst : Field κ] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) κ) (a : Fin n → κ),
    Function.Injective a →
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (a i)) →
        ∃ (P : GL (Fin n) κ),
          M * (↑P : Matrix (Fin n) (Fin n) κ) = (↑P : Matrix (Fin n) (Fin n) κ) * Matrix.diagonal a := by
  intro κ _ n M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  have hU : IsUnit (Matrix.of fun r c => v c r : Matrix (Fin n) (Fin n) κ) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext r c
  have h := congrFun (hv c).apply_eq_smul r
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h
