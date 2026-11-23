import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField midDeg midVar ptCoord noCoord ptIdx noIdx
  ptFlagModel)

def PairNumberJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord w z))) d →
    fnField O (joinCoord x (joinCoord w z)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ ι')))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord w z))) d
          (fun i => midDeg (K₂ := K₂) (a i)) (fun i => midDeg (K₂ := K₂) (a' i))
          (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
