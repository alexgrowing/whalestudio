import Mathlib

noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder

namespace PI.Bochner

def PD {Γ : Type} [AddCommGroup Γ] (φ : Γ → ℂ) : Prop :=
  ∀ (N : ℕ) (g : Fin N → Γ) (c : Fin N → ℂ),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * φ (g i - g j)

def StepGNS : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ] (φ : Γ → ℂ), PD φ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (U : Γ → H →L[ℂ] H) (ξ : H),
      U 0 = 1 ∧ (∀ a b, U (a + b) = U a * U b) ∧ (∀ a, star (U a) = U (-a)) ∧
        ∀ γ, φ γ = inner ℂ ξ (U γ ξ)

def StepAlg : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Γ → H →L[ℂ] H) (ξ : H),
    U 0 = 1 → (∀ a b, U (a + b) = U a * U b) → (∀ a, star (U a) = U (-a)) →
    ∃ (A : Type) (_ : CommCStarAlgebra A) (u : Multiplicative Γ →* unitary A) (ω : A →ₗ[ℂ] ℂ),
      (∀ a, 0 ≤ ω (star a * a)) ∧
        ∀ γ : Γ, ω (u (Multiplicative.ofAdd γ) : A) = inner ℂ ξ (U γ ξ)

def StepRiesz : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Λ : C(X, ℂ) →ₗ[ℂ] ℂ), (∀ f, 0 ≤ Λ (star f * f)) →
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ

def StepGelfand : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ] (A : Type) [CommCStarAlgebra A]
    (u : Multiplicative Γ →* unitary A) (ω : A →ₗ[ℂ] ℂ), (∀ a, 0 ≤ ω (star a * a)) →
    letI : TopologicalSpace (Multiplicative Γ) := ⊥
    letI : MeasurableSpace (PontryaginDual (Multiplicative Γ)) := borel _
    ∃ μ : Measure (PontryaginDual (Multiplicative Γ)), IsFiniteMeasure μ ∧
      ∀ γ : Γ, ω (u (Multiplicative.ofAdd γ) : A)
        = ∫ χ, ((χ (Multiplicative.ofAdd γ) : Circle) : ℂ) ∂μ

end PI.Bochner
