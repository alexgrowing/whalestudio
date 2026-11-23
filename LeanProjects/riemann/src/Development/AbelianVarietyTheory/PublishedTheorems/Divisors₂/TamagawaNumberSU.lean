import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal

namespace GlobalTheory.Published

open GlobalTheory.TamSU

def TamagawaNumberSU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J →
    ∀ Λ : Submodule (𝓞 E) (Fin M → E), Λ.FG → Submodule.span E (Λ : Set (Fin M → E)) = ⊤ →
      Summable (fun v : HeightOneSpectrum (𝓞 F) => locVol σ J Λ v - 1) ∧
      ∀ (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf F ⊗[F] E →+* ℂ)) (e : Fin (M ^ 2 - 1) → Matrix (Fin M) (Fin M) E),
        (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
        (∀ i, e i ∈ lieInt σ J Λ) → LinearIndependent F e →
        ∀ μ : Measure (SUAdelic σ J), IsTamagawa σ J Λ Ψ θ e μ →
          ∀ 𝓕 : Set (SUAdelic σ J), IsFundamentalDomain ((SURat σ J).subgroupOf (SUAdelic σ J)) 𝓕 μ → μ 𝓕 = 1

end GlobalTheory.Published
