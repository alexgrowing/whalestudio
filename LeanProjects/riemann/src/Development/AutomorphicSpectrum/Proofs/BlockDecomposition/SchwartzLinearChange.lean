import Mathlib
open scoped Matrix SchwartzMap

namespace GlobalTheory.CompanionTheory.KlocopSw

noncomputable def rightMulEquiv (m n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) :
    (Fin m → Fin n → ℂ) ≃L[ℂ] (Fin m → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show ((Matrix.of u + Matrix.of v) * a : Matrix (Fin m) (Fin n) ℂ) =
          Matrix.of u * a + Matrix.of v * a
        rw [Matrix.add_mul]
      map_smul' := fun r u => by
        show ((r • Matrix.of u) * a : Matrix (Fin m) (Fin n) ℂ) = r • (Matrix.of u * a)
        rw [Matrix.smul_mul]
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      left_inv := fun u => by
        show (Matrix.of u * a * a⁻¹ : Matrix (Fin m) (Fin n) ℂ) = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.mul_one]
        rfl
      right_inv := fun u => by
        show (Matrix.of u * a⁻¹ * a : Matrix (Fin m) (Fin n) ℂ) = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul a ha, Matrix.mul_one]
        rfl }

theorem exists_schwartz_rightMul : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  intro m n c a ha φ
  refine ⟨c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((rightMulEquiv m n a ha).restrictScalars ℝ) φ, ?_⟩
  funext u
  rfl

end GlobalTheory.CompanionTheory.KlocopSw
