import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def InertiaRam : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [Field E] [NumberField E] (s : E ≃+* E) (δ : E)
    (φ : E →+* ℂ_[p]), δ ^ 2 = -(p : E) → s δ = -δ → (∀ y, s (s y) = y) →
    (∀ y : E, s y = y → φ y ∈ MaximalUnramifiedExtension p) →
    ‖φ δ‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) ∧
    (∀ y : 𝓞 E, ‖φ (y : E) - φ (s (y : E))‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ)) ∧
    (∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ ‖φ δ‖)

def EmbSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois ℚ E] (φ ψ₁ ψ₂ : E →+* ℂ_[p]),
    (∃ π : 𝓞 K, ‖φ (algebraMap K E (π : K))‖ < 1 ∧
      ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ ‖φ (algebraMap K E (π : K))‖) →
    (∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) →
    (∀ y : 𝓞 E, ‖φ (y : E) - ψ₂ (y : E)‖ < 1) →
    ψ₁ ≠ ψ₂ →
    ∃ y : 𝓞 E, ‖φ (y : E) - ψ₁ (y : E)‖ = 1

def SepPairs : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (c s : E ≃+* E)
    (δ : E), δ ^ 2 = -(p : E) → c δ = -δ → s δ = -δ → (∀ y, c (c y) = y) → (∀ y, s (s y) = y) →
    (∀ y, s (c y) = c (s y)) →
    ∀ (H : Type) (emb : Bool × H → (E →+* ℂ_[p])), Function.Injective emb →
    (∀ τ ρ, emb τ δ = emb ρ δ) → (∀ t y, emb (true, t) y = emb (false, t) (s (c y))) →
    (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) →
    ∀ τ ρ : Bool × H, ρ ≠ (!τ.1, τ.2) → ∃ e : 𝓞 E, ‖emb τ (e : E) - emb ρ (c (e : E))‖ = 1

def KurGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] (φ : E →+* ℂ_[p]) (S : Set E),
    (∀ g ∈ S, φ g ∈ MaximalUnramifiedExtension p) → ∀ y ∈ Subfield.closure S, φ y ∈ MaximalUnramifiedExtension p

end Formalism.L2.Th1.GD
