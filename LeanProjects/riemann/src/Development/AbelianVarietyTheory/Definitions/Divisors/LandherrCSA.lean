import Mathlib

noncomputable section
namespace GlobalTheory.HermCSA
open NumberField
open scoped TensorProduct

def IsUInv (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] (s : C →+ C) : Prop :=
  (∀ x y, s (x * y) = s y * s x) ∧ (∀ x, s (s x) = x) ∧
    ∀ a : F, s (algebraMap F C a) = algebraMap F C (IsCMField.complexConj F a)

def ext (C K : Type) [Ring C] [CommRing K] (s : C →+ C) : K ⊗[ℤ] C →ₗ[ℤ] K ⊗[ℤ] C :=
  LinearMap.lTensor K s.toIntLinearMap

def LandherrCSA : Prop :=
  ∀ (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (s : C →+ C), IsUInv F C s →
    ∀ A A' : C, IsUnit A → IsUnit A' → s A = A → s A' = A' →
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (g : (ℚ_[ℓ] ⊗[ℤ] C)ˣ) (ν : ℚ_[ℓ]), ν ≠ 0 ∧
      (1 : ℚ_[ℓ]) ⊗ₜ A' = ν • (ext C ℚ_[ℓ] s (g : ℚ_[ℓ] ⊗[ℤ] C) * ((1 : ℚ_[ℓ]) ⊗ₜ A) * (g : ℚ_[ℓ] ⊗[ℤ] C))) →
    (∃ g : (ℝ ⊗[ℤ] C)ˣ, (1 : ℝ) ⊗ₜ A' = ext C ℝ s (g : ℝ ⊗[ℤ] C) * ((1 : ℝ) ⊗ₜ A) * (g : ℝ ⊗[ℤ] C)) →
    ∃ (g : Cˣ) (c : F), IsCMField.complexConj F c = c ∧ (∀ τ : F →+* ℂ, 0 < (τ c).re) ∧
      A' = algebraMap F C c * (s (g : C) * A * g)

end GlobalTheory.HermCSA
