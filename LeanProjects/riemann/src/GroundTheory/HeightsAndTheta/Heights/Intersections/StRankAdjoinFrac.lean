import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

abbrev adjoinInclAlgebra (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) :
    Algebra (Algebra.adjoin F S) (Algebra.adjoin F T) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom.toAlgebra

def RankAdjoinFrac.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (S T : Set Ω) (h : S ⊆ T),
    letI := adjoinInclAlgebra F h
    Module.finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
