import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def SegreModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ (N : ℕ) (e : (∀ k, ι k) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω),
      (∀ c, x (e c) = ∏ k, y ⟨k, c k⟩) ∧ x ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra R Ω], IndefiniteRowSideFullHecke.Kleiman2.SameModel R y (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
