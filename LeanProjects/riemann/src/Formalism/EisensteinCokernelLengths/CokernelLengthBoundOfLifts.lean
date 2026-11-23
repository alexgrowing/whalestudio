import Mathlib
import Formalism.FrobeniusContraction.Statement
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

noncomputable section

open Classical

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts

open Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.V2

def FrobFixedPointLift : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h k : ℕ) (y : ZMod n → V),
    h < (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    IsAdicComplete B.I ↥(W.XMN M) →
    (∀ j, B.q ^ k • y j ∈ W.N j) → W.Γ y - y ∈ W.XMN M →
    ∃ z ∈ W.XMN M, W.Φ z - z = W.Γ y - y ∧ (y, z) ∈ W.Zf

def LenBound2 : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def CokernelLengthBoundOfLifts : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V₁ : Type) [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
    [Module O V₁] [IsScalarTower O AA V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
    [Module O V₂] [IsScalarTower O AA V₂]
    (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) (h : Hom W₁ W₂) (g g₀ e e' : ℕ)
    (s₀ : Finset ((ZMod n → V₂) × (ZMod n → V₂))),
    W₂.FIN g → s₀.card ≤ g₀ → (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))) ⊆ W₂.Zf →
    (∀ p ∈ W₂.Zf, (B.ℓ ^ e : ℕ) • p ∈ Submodule.span O (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))) ⊔ h.Im) →
    (∀ p ∈ Submodule.span O (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))), (B.ℓ ^ e' : ℕ) • p ∈ h.Im) →
    h.col ≤ ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) *
      Module.length O (O ⧸ Ideal.span {(B.ℓ : O)})

def IntV {A : Type} [CommRing A] [IsDomain A] {ι : Type} (x : ι → FractionRing A) : Prop :=
  ∀ i, ∃ a : A, x i = algebraMap A (FractionRing A) a

def SatCap : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (ι : Type) [Fintype ι]
    (ℓ π₀ Λ : A), IsRelPrime ℓ π₀ → ∀ N : Submodule A (ι → FractionRing A),
    (∀ x : ι → FractionRing A, IntV x → Λ • x ∈ N) →
    (∀ x ∈ N, IntV (Λ • x)) →
    (∀ x : ι → FractionRing A, IntV (Λ • x) → (∃ k : ℕ, ℓ ^ k • x ∈ N) → x ∈ N) →
    ∀ x : ι → FractionRing A,
      (IntV (Λ • x) ∧ ∃ m ∈ N, ∃ p : ι → FractionRing A, (∃ k : ℕ, IntV (ℓ ^ k • p)) ∧
          x = π₀ • m + (π₀ * Λ) • p) ↔
        ∃ m ∈ N, x = π₀ • m

def ResidueBlockAvoidsFrobenius : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), 0 ≤ σ →
    (G = true → 1 ≤ w ∧ w + t - 1 ≤ η) →
    (G = false → (h : ℤ) - η ≤ w ∧ (w : ℤ) + t - 1 ≤ (h : ℤ) - 1) →
    (η : ℤ) + 4 * σ + 6 < ℓ →
    (∀ x ∈ U.filter (fun x => InWinN G h η x), ∀ y ∈ Finset.Icc (w : ℤ) (w + t - 1),
      σ + 2 < |x - y|) →
    ResidueAvoidance ℓ G h η σ U →
    ∀ u ∈ U, ∀ y ∈ Finset.Icc (w : ℤ) (w + t - 1), ∀ d : ℤ, |d| ≤ σ →
      ((u + d : ℤ) : ZMod ℓ) ≠ ((y : ℤ) : ZMod ℓ)

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts
