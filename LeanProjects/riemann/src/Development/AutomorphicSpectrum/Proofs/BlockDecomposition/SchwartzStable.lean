import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementSectionC

open Ad3.K.LC

noncomputable def rightMulLin (h : GL (Fin 3) ℂ) :
    (M23 × (Fin 2 → ℂ)) ≃ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun v := (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  invFun v := (Matrix.of.symm (Matrix.of v.1 * ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  map_add' v w := by
    refine Prod.ext ?_ rfl
    exact Matrix.add_mul (Matrix.of v.1) (Matrix.of w.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  map_smul' c v := by
    refine Prod.ext ?_ rfl
    exact Matrix.smul_mul c (Matrix.of v.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  left_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ))) *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]
  right_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))) * (h : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]

theorem exists_rightTranslate (h : GL (Fin 3) ℂ) (Ψ : Sw) :
    ∃ Ψ' : Sw, ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulLin h).toContinuousLinearEquiv Ψ,
    fun _ _ => rfl⟩

theorem inn_smul (c : ℂ) (Ψ : Sw) (g : GL (Fin 3) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn (c • Ψ) g M t = c * inn Ψ g M t := by
  unfold inn
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem inn_mul_right (Ψ Ψ₀ : Sw) (g h : GL (Fin 3) ℂ)
    (hΨ : ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ₀ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q))
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn Ψ (g * h) M t = inn Ψ₀ g M t := by
  unfold inn
  congr 1
  funext p
  rw [hΨ, Units.val_mul, ← Matrix.mul_assoc]
  simp

theorem stStable : StStable := by
  intro k _ Ψ h
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_rightTranslate h Ψ
  set c : ℂ := ((‖(h : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) with hc
  refine ⟨c • Ψ₀, ?_⟩
  funext g
  unfold sec
  simp only [inn_smul, inn_mul_right Ψ Ψ₀ g h hΨ₀]
  have hdet : ((‖((g * h : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) =
      ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) * c := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, mul_pow, Complex.ofReal_mul]
  have hin : ∀ y : M22, (∫ t : ℂ, c * inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) =
      c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t := by
    intro y
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  have hout : (∫ y : M22, (c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)) =
      c * ∫ y : M22, (∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp only [hin]
  rw [hdet, hout]
  ring

end GlobalTheory.CompanionTheory.GodementSectionC
