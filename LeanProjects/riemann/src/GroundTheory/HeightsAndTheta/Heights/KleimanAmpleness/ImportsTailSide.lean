import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreTwist.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (β : K → ℤ) (c : ℤ),
      secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg (Sum.inl ())) =
        secOver S y (β + fun _ => c)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
