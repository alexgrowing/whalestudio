import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellDSq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), cellD S y (n + 1) (cellD S y n s) = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
