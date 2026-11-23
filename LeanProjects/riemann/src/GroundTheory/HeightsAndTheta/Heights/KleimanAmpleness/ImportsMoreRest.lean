import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def GenericFibreScalars.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] (F : Type) [Field F] [Algebra S F] (Ω : Type) [Field Ω] [Algebra S Ω]
    [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F] (N N' : ℕ) (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω),
    IsNoetherianRing S → x' ≠ 0 → Kleiman.IsDomination S x x' →
    IndefiniteRowSideFullHecke.Kleiman2.SameModel F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) →
    ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ Kleiman.domRing S x x' i, ∃ s : S,
      algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s * b ∈ Kleiman.chartRing S x (Kleiman.singleChart hi)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
