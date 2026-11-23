import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def FinrankAdjoinRange.Statement : Prop :=
  ∀ (F Φ Ω : Type) [Field F] [Field Φ] [Field Ω] [Algebra F Φ] [Algebra F Ω] [Algebra Φ Ω] [IsScalarTower F Φ Ω]
    (S : Set Ω),
    Module.finrank Φ (IntermediateField.adjoin Φ S) =
      IntermediateField.relfinrank (IsScalarTower.toAlgHom F Φ Ω).fieldRange
        ((IsScalarTower.toAlgHom F Φ Ω).fieldRange ⊔ IntermediateField.adjoin F S)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
