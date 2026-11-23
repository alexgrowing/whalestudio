import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelOfBlockGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → BlockGen S y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
