import ReciprocityTheory.DualLattices.BadStatement
import ReciprocityTheory.DualLattices.CotangentSurjective

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def CokernelsAgreeEquivariantly : Prop :=
  ∀ (S A : Type) [CommRing S] [CommRing A] [Algebra S A]
    (T₁ T₂ Q : Type) [AddCommGroup T₁] [AddCommGroup T₂] [AddCommGroup Q]
    [Module S T₁] [Module S T₂] [Module S Q] [Module.Projective S Q]
    (ω₁ ω₂ Ω : Type) [AddCommGroup ω₁] [AddCommGroup ω₂] [AddCommGroup Ω]
    [Module A ω₁] [Module A ω₂] [Module A Ω]
    (ι : T₁ →ₗ[S] T₂) (q : T₂ →ₗ[S] Q) (j : ω₁ →ₗ[A] ω₂) (p : ω₂ →ₗ[A] Ω)
    (α₁ : A ⊗[S] T₁ →ₗ[A] ω₁) (α₂ : A ⊗[S] T₂ →ₗ[A] ω₂) (β : A ⊗[S] Q →ₗ[A] Ω),
    Function.Injective ι → Function.Exact ι q → Function.Surjective q →
    Function.Injective j → Function.Exact j p →
    α₂ ∘ₗ ι.baseChange A = j ∘ₗ α₁ → p ∘ₗ α₂ = β ∘ₗ q.baseChange A → Function.Bijective β →
    ∀ (O : Type) [Ring O] (ρ₁ : O → T₁ →ₗ[S] T₁) (ρ₂ : O → T₂ →ₗ[S] T₂) (lam₁ : O → ω₁ →ₗ[A] ω₁)
      (lam₂ : O → ω₂ →ₗ[A] ω₂),
      (∀ a, j ∘ₗ lam₁ a = lam₂ a ∘ₗ j) →
      (∀ a, α₁ ∘ₗ (ρ₁ a).baseChange A = lam₁ a ∘ₗ α₁) →
      (∀ a, α₂ ∘ₗ (ρ₂ a).baseChange A = lam₂ a ∘ₗ α₂) →
      ∃ E : (ω₁ ⧸ LinearMap.range α₁) ≃ₗ[A] (ω₂ ⧸ LinearMap.range α₂),
        (∀ x, E (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x)) ∧
        ∀ a, ∀ z, ∃ h₁ h₂, E ((LinearMap.range α₁).mapQ (LinearMap.range α₁) (lam₁ a) h₁ z) =
          (LinearMap.range α₂).mapQ (LinearMap.range α₂) (lam₂ a) h₂ (E z)

end ReciprocityTheory.PGsh.Up
