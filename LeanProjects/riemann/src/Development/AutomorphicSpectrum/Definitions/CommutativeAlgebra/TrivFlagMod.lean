import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim

namespace GlobalTheory.CompanionTheory.Ar.Num

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]

def IsLatFamily (x : (Σ k, ι k) → Ω) (Γ : (∀ k, ι k) → AddSubgroup V) : Prop :=
  (∀ s, mseg x s ≠ 0 → ∀ a ∈ chartRing o (mseg x) s, ∀ v ∈ Γ s, a • v ∈ Γ s) ∧
  ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∀ v ∈ Γ s, ∃ m : ℕ, (mseg x s / mseg x t) ^ m • v ∈ Γ t

def IsQuotHom (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (Γ : (∀ k, ι k) → AddSubgroup (V × V₁)) : Prop :=
  IsLatFamily o x Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v w, (v, w) ∈ Γ s → v ∈ A s ∧ w ∈ B s) ∧ (∀ v ∈ A s, ∃ w, (v, w) ∈ Γ s) ∧
    (∀ w, (0, w) ∈ Γ s ↔ w ∈ B' s) ∧ (∀ v ∈ A' s, (v, 0) ∈ Γ s)

def QuotEquiv (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  ∃ Γ, IsQuotHom o x A A' B B' Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ w ∈ B s, ∃ v, (v, w) ∈ Γ s)

def QuotExact (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (C C' : (∀ k, ι k) → AddSubgroup V₂) : Prop :=
  ∃ Γ Δ, IsQuotHom o x A A' B B' Γ ∧ IsQuotHom o x B B' C C' Δ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ c ∈ C s, ∃ b, (b, c) ∈ Δ s) ∧
    (∀ b, (b, 0) ∈ Δ s ↔ ∃ a, (a, b) ∈ Γ s)

def IsScaled (x : (Σ k, ι k) → Ω) (c : Ω) (A A' : (∀ k, ι k) → AddSubgroup V) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A' s ↔ ∃ e ∈ A s, v = c • e

def IsLine (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) (A : (∀ k, ι k) → AddSubgroup Ω) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A s ↔ ∃ r ∈ chartRing o (mseg x) s, v = r * (u * chartMon x s a)

def IsDualLat (x : (Σ k, ι k) → Ω) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (A : (∀ k, ι k) → AddSubgroup V)
    (B : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  Function.Bijective β.flip ∧
    ∀ s, mseg x s ≠ 0 → ∀ w, w ∈ B s ↔ ∀ v ∈ A s, β v w ∈ chartRing o (mseg x) s

def TrivFlagMod (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ) : Prop :=
  ∃ g : (∀ k, ι k) → Matrix (Fin N) (Fin N) Ω,
    (∀ s, mseg x s ≠ 0 → (∀ i j, g s i j ∈ chartRing o (mseg x) s) ∧
      ∃ h ∈ chartRing o (mseg x) s, ∃ r ∈ chartRing o (mseg x) s,
        (g s).det * h = 1 + algebraMap o Ω ϖ * r) ∧
    ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∃ (m : ℕ) (U Z : Matrix (Fin N) (Fin N) Ω),
      (∀ i j, U i j ∈ chartRing o (mseg x) t) ∧ (∀ i j, Z i j ∈ chartRing o (mseg x) t) ∧
      (∀ i j, j < i → U i j = 0) ∧
      (∀ i, U i i = (mseg x s / mseg x t) ^ m * (chartMon x s (b i) / chartMon x t (b i))) ∧
      (∀ i j, (mseg x s / mseg x t) ^ m * g s i j ∈ chartRing o (mseg x) t) ∧
      (mseg x s / mseg x t) ^ m • g s = g t * U + algebraMap o Ω ϖ • Z

end GlobalTheory.CompanionTheory.Ar.Num
