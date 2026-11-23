import Mathlib

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKInvGood

def locOrder (ℓ : ℕ) [Fact ℓ.Prime] {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
  Algebra.adjoin ℤ_[ℓ] ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (OB : Set B))

def cenOrder (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F] :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
  Algebra.adjoin ℤ_[ℓ] (Set.range fun a : NumberField.RingOfIntegers F => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F))

def cenMap (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) ((Algebra.ofId F B).restrictScalars ℚ)

def CentreCompat (ℓ : ℕ) [Fact ℓ.Prime] {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) {n : ℕ}
    (ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F)) : Prop :=
  ∀ a : cenOrder ℓ F, ∃ h : cenMap ℓ F B (a : ℚ_[ℓ] ⊗[ℚ] F) ∈ locOrder ℓ OB,
    ψ ⟨_, h⟩ = Matrix.scalar (Fin n) a

end GlobalTheory.LKInvGood
