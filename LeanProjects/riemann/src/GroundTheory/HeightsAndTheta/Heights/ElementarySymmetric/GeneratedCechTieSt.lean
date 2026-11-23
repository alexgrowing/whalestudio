import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.RayGenVanishSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver GeneratedV)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsGenerated baseDeg pnPt isModelWithBase_pnPt)

def GeneratedCechTie.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsGenerated S y β → GeneratedV S (mIdealOver S y) β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
