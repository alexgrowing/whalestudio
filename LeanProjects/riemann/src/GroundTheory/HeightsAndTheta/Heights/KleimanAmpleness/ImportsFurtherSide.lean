import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelInvariants.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y' →
    (IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y ↔ IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y') ∧
      (IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
