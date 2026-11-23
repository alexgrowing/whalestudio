import Mathlib
namespace UpperTheory.Reformulated.B.OrderedFlagDiagonal
abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

variable {K : Type} [Field K]

theorem ordFlag_diag (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (hX : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' X) (c j) := by
    intro j
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hX,
      Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  choose v hv using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) c hc v hv
  have hU : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin 4) (Fin 4) K) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext i j
  have h := congrFun (hv j).apply_eq_smul i
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.OrderedFlagDiagonal
