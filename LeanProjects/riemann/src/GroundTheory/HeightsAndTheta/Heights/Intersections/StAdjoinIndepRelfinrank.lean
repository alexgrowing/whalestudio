import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def AdjoinIndepRelfinrank.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (L₀ L : IntermediateField F Ω) (ι : Type) (t : ι → Ω),
    L₀ ≤ L → AlgebraicIndependent L t →
      IntermediateField.relfinrank (L₀ ⊔ IntermediateField.adjoin F (Set.range t))
          (L ⊔ IntermediateField.adjoin F (Set.range t)) =
        IntermediateField.relfinrank L₀ L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
