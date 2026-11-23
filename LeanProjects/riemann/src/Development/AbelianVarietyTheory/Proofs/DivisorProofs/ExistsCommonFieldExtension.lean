import Mathlib

open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_field_extension :
    ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂),
      ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  intro Ω Ω₁ Ω₂ _ _ _ i₁ i₂
  letI : Algebra Ω Ω₁ := i₁.toAlgebra
  letI : Algebra Ω Ω₂ := i₂.toAlgebra
  haveI : Nontrivial (Ω₁ ⊗[Ω] Ω₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω₁ ⊗[Ω] Ω₂)
  refine ⟨(Ω₁ ⊗[Ω] Ω₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := Ω) (A := Ω₁) (B := Ω₂)).toRingHom, ?_⟩
  ext x
  have h : (algebraMap Ω Ω₁ x) ⊗ₜ[Ω] (1 : Ω₂) = (1 : Ω₁) ⊗ₜ[Ω] (algebraMap Ω Ω₂ x) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact congrArg (Ideal.Quotient.mk m) h

end GlobalTheory
