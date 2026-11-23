import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts modVec resImage)

def RestrictionPointsAll.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      modelPts S (modVec S y c p) =
        {z' | ∃ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p ∧
          z' = Subring.closure (resImage S y c p z)}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
