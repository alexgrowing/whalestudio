import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.ThetaUniq

def cosetInd (F : Type) [Field F] [NumberField F] {κ : Type} (N : ℕ) (d : κ → F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator {x | ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
    x i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i) + N • u} 1

end GlobalTheory.CompanionTheory.ThetaUniq

end
