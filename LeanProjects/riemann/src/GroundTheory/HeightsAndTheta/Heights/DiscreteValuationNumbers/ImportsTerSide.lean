import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField ptCoord noCoord pt_model join_model
  ptFlagModel)

def JoinTwoModels.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver O (mcIdeal O x) d →
    ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (z₁ : (Σ k, ι₁ k) → Ω)
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (z₂ : (Σ k, ι₂ k) → Ω),
      IsModelOver O (mcIdeal O (joinCoord x z₁)) d → fnField O (joinCoord x z₁) = fnField O x →
      IsModelOver O (mcIdeal O (joinCoord x z₂)) d → fnField O (joinCoord x z₂) = fnField O x →
      IsModelOver O (mcIdeal O (joinCoord x (joinCoord z₁ z₂))) d ∧
        fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x

end GroundTheory.Heights₂.Heights.NumbersDVR
