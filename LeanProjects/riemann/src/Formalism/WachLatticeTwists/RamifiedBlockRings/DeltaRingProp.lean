import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

def DeltaRingProp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X d G : Type)
    [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (bl : d → Fin (t + 1)) (T : Subalgebra O (X → O))
    (r₀ : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G) (eB e₁ s : X → Matrix d d O)
    (D : RingData O X d G t bl), RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D →
    ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ y : Oˣ, ((ε g₀ : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O) →
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    IsDiscreteValuationRing.addVal O D.δO =
      eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    IsDiscreteValuationRing.addVal O D.δO ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
