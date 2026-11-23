import Mathlib

noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Classical in

def PlaceIdemSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (P : Ideal (𝓞 E)), P.IsPrime → P ≠ ⊥ →
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (a : Fin n → V), ∀ ψ : E →+* k,
      ∑ i, algebraMap V k (a i) * ψ (b i : E) =
        if (∀ x : 𝓞 E, x ∈ P ↔ ψ (x : E) ∈ algebraMap V k '' (IsLocalRing.maximalIdeal V : Set V)) then 1 else 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
