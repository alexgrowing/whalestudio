import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

namespace GlobalTheory.TwFin

def TwFin {H : Type} [Group H] (θ : H →* H) (K : Subgroup H) (δ N : H) : Prop :=
  ∀ E : Finset H, ∃ D : Finset H, ∀ t : H, t * N = N * t → (∃ e ∈ E, ∃ k ∈ K, t⁻¹ * δ * θ t = e * k) →
    ∃ u ∈ GlobalTheory.BCT.twCent θ δ, ∃ d ∈ D, ∃ k ∈ K, t = u * d * k

end GlobalTheory.TwFin
