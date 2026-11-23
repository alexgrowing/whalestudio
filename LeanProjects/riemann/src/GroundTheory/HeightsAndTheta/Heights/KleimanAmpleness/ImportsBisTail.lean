import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def BlockGenTransfer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    BlockGen S y k₀ →
    ∀ (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → mIdealOver S y ≤ mIdealOver S y' → BlockGen S y' k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
