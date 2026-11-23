import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ β : K → ℤ,
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
