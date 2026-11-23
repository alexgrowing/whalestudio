import Mathlib

namespace Formalism.L2.Props

open Filter Topology IsDedekindDomain NumberField

def LogCycConv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ L : ℚ_[l],
    Tendsto (fun k : ℕ => ((((u : ℤ_[l]) : ℚ_[l]) ^ ((l - 1) * l ^ k) - 1) / (((l - 1) * l ^ k : ℕ) : ℚ_[l])))
      atTop (𝓝 L)

def PlaceEmbExists : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    (∀ x : F, algebraMap F Ω x ∈ A ↔ v.valuation F x ≤ 1) →
    ∃ i : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F), ∀ x : Ω, x ∈ A ↔
      ∃ q : Polynomial (v.adicCompletion F), q.Monic ∧ (∀ k, q.coeff k ∈ v.adicCompletionIntegers F) ∧
        Polynomial.aeval (i x) q = 0

def IntAdelesCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

def TameTrivOnZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime →
    Nat.card (𝓞 E ⧸ v.asIdeal) = g →
    ∀ ξ : (v.adicCompletion E)ˣ →* ℂˣ,
      (∀ u : (v.adicCompletion E)ˣ, Valued.v ((u : v.adicCompletion E) - 1) < 1 → ξ u = 1) →
      (∀ (m : ℤ) (u : (v.adicCompletion E)ˣ), ¬ (g : ℤ) ∣ m → (u : v.adicCompletion E) = (m : v.adicCompletion E) → ξ u = 1) →
      ∀ u : (v.adicCompletion E)ˣ, Valued.v (u : v.adicCompletion E) = 1 → ξ u = 1

end Formalism.L2.Props
