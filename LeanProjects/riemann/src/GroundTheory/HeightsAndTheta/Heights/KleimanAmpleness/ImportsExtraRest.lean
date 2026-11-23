import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelWithBaseLocalization.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K)
    (S' : Type) [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
    (M : Submonoid S) [IsLocalization M S'],
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S' y k₀

example (h : ModelWithBaseLocalization.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () exF
    (nonZeroDivisors exO) isModelWithBase_exO_pnPt

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
