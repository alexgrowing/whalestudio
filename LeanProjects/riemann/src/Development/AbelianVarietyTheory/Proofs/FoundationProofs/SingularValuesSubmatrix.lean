import Mathlib

namespace GlobalTheory

open Module

theorem singularValues_linearIsometryEquiv_comp {E E' F F' : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [FiniteDimensional ℂ F']
    (T : E →ₗ[ℂ] F) (e : E' ≃ₗᵢ[ℂ] E) (f : F ≃ₗᵢ[ℂ] F') :
    (f.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ e.toLinearEquiv.toLinearMap).singularValues =
      T.singularValues := by
  set S := f.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ e.toLinearEquiv.toLinearMap with hS
  have hadj : LinearMap.adjoint S =
      e.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.adjoint T ∘ₗ f.symm.toLinearEquiv.toLinearMap := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp only [hS, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply,
      LinearMap.adjoint_inner_left, ← LinearIsometryEquiv.inner_map_map f.symm,
      LinearIsometryEquiv.symm_apply_apply]
  have hA : LinearMap.adjoint S ∘ₗ S = e.symm.toLinearEquiv.conj (LinearMap.adjoint T ∘ₗ T) := by
    rw [hadj]
    ext x
    simp [hS, LinearEquiv.conj_apply]
  have hn : finrank ℂ E' = finrank ℂ E := e.toLinearEquiv.finrank_eq
  ext i
  by_cases hi : i < finrank ℂ E
  · rw [S.singularValues_of_lt hn hi, T.singularValues_of_lt rfl hi]
    have heig : S.isSymmetric_adjoint_comp_self.eigenvalues hn =
        T.isSymmetric_adjoint_comp_self.eigenvalues rfl := by
      rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff, hA, LinearEquiv.charpoly_conj]
    rw [heig]
  · push_neg at hi
    rw [S.singularValues_of_finrank_le (hn ▸ hi), T.singularValues_of_finrank_le hi]

theorem toEuclideanLin_submatrix (p q : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (α : ι ≃ Fin p) (β : κ ≃ Fin q) (B : Matrix (Fin p) (Fin q) ℂ) :
    (Matrix.toEuclideanLin (B.submatrix α β) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι) =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ α.symm).toLinearEquiv.toLinearMap ∘ₗ
        (Matrix.toEuclideanLin B : EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)) ∘ₗ
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ β).toLinearEquiv.toLinearMap := by
  ext x i
  simp [Matrix.toEuclideanLin, LinearIsometryEquiv.piLpCongrLeft_apply, Matrix.mulVec, dotProduct]

theorem singularValues_submatrix : ∀ (p q : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (α : ι ≃ Fin p) (β : κ ≃ Fin q) (B : Matrix (Fin p) (Fin q) ℂ), (Matrix.toEuclideanLin (B.submatrix α β) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι).singularValues = (Matrix.toEuclideanLin B : EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues := by
  intro p q ι κ _ _ _ _ α β B
  rw [toEuclideanLin_submatrix]
  exact singularValues_linearIsometryEquiv_comp _ _ _

end GlobalTheory
