import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def KinE {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : IntermediateField ℚ (hostE ζ a b) :=
  ℚ⟮bE ζ a b⟯

def HostDiffSupport : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime →
    P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) →
      ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∈ P ∨ ((q : ℤ) : 𝓞 (hostE ζ a b)) ∈ P

def HostPrincipal : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) ∧ 𝔟 ⊔ σ • 𝔟 = ⊤

end Formalism.FrobeniusOrbits
