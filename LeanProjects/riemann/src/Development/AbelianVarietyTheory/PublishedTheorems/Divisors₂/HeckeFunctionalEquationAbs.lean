import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published

def HeckeFunctionalEquationAbs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ Λ' : ℂ → ℂ), IsUnitary χ →
      Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → (∀ v, ExpAt χ v (a v)) → IsCompletedL χ n Λ →
      IsCompletedL χ⁻¹ (fun i => -n i) Λ' → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s : ℂ,
        Λ s = ε * ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) * Λ' (1 - s)

end GlobalTheory.Published

end
