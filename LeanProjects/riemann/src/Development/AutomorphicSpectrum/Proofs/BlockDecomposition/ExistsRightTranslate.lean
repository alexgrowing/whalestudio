import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchwartzTranslateC

noncomputable def rightMulLin (h : GL (Fin 3) ℂ) : Ad3.K.LC.M23 ≃ₗ[ℝ] Ad3.K.LC.M23 where
  toFun X := Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ))
  invFun X := Matrix.of.symm (Matrix.of X * ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))
  map_add' X Y := by
    exact Matrix.add_mul (Matrix.of X) (Matrix.of Y) (h : Matrix (Fin 3) (Fin 3) ℂ)
  map_smul' c X := by
    exact Matrix.smul_mul c (Matrix.of X) (h : Matrix (Fin 3) (Fin 3) ℂ)
  left_inv X := by
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ))) *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = X
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]
  right_inv X := by
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of X *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))) * (h : Matrix (Fin 3) (Fin 3) ℂ)) = X
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]

noncomputable def rightMulProd (h : GL (Fin 3) ℂ) :
    (Ad3.K.LC.M23 × (Fin 2 → ℂ)) ≃L[ℝ] (Ad3.K.LC.M23 × (Fin 2 → ℂ)) :=
  ((rightMulLin h).prodCongr (LinearEquiv.refl ℝ (Fin 2 → ℂ))).toContinuousLinearEquiv

theorem exists_rightTranslate :
    ∀ (h : GL (Fin 3) ℂ) (Ψ : Ad3.K.LC.Sw), ∃ Ψ' : Ad3.K.LC.Sw,
      ∀ (X : Ad3.K.LC.M23) (q : Fin 2 → ℂ),
        Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q) := by
  intro h Ψ
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulProd h) Ψ, fun X q => rfl⟩

end GlobalTheory.CompanionTheory.SchwartzTranslateC
