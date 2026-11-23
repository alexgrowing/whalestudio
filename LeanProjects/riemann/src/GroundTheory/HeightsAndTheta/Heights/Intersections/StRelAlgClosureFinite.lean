import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RelAlgClosureFinite.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (S : Finset L),
    IntermediateField.adjoin K (S : Set L) = ⊤ → FiniteDimensional K (algebraicClosure K L)

end GroundTheory.Heights₂.Heights.Inter
