import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ValPolyLineX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

def FlagGenericPoint.Statement : Prop :=
  ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d →
    ∃ z ∈ mcPts P, ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = 0 → f ∈ P

namespace FlagGenericPoint

open Line

end FlagGenericPoint

end GroundTheory.Heights₂.Heights.LowerBoundFree
