import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def InvOpenInside.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [QuasiCompact f] (p : Nat.Primes) (W : X.Opens),
    Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ invOpen f m ≤ W

end

end GroundTheory.Heights₂.Heights.Model
