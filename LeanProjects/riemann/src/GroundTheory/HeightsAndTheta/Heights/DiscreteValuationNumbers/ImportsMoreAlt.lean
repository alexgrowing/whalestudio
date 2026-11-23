import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord midDeg midVar ptCoord ptFlagModel)

def JoinVerticalDivisorRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord w z))) (midDeg (K₂ := K₂) b)
      (rename (midVar ι₂) f) (rename (midVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
