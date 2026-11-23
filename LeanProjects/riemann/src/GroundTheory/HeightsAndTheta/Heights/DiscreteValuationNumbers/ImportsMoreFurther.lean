import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def VerticalDivisorCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (ϖ : O)
    (b : K → ℤ) (f g : MRing ι O), Irreducible ϖ → IsMultiProjPrime P →
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g ↔ IsVerticalDivisor P ϖ b f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
