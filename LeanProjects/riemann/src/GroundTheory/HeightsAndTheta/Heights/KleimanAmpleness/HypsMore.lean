import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def SecOverLocalization.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    (S' : Type) [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
    (M : Submonoid S) [IsLocalization M S'],
    secOver S' y β = Submodule.span S' (secOver S y β : Set Ω)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
