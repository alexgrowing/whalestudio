import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def BlockGenOfModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → BlockGen S y k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
