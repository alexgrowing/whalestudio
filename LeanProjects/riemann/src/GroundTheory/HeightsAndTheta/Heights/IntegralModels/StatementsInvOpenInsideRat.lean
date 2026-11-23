import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def InvOpenInsideRat.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (W : X.Opens),
    Set.range (baseChangeMap f ℚ) ⊆ Set.range W.ι →
    ∃ m : ℕ, 0 < m ∧ invOpen f m ≤ W

end

end GroundTheory.Heights₂.Heights.Model
