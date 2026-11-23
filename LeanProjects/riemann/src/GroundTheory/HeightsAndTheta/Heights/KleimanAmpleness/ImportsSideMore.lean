import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)),
    (∀ k, (I k).Nonempty) → CellMeets y I →
      chartSecOver S y k₀ e γ J ⊆ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
