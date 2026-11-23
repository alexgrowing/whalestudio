import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RankFracDegree.Statement : Prop :=
  ∀ (F Ω A B : Type) [Field F] [Field Ω] [Algebra F Ω] [CommRing A] [CommRing B] [Algebra A B]
    (L₀ L : IntermediateField F Ω) (f : A →+* Ω) (g : B →+* Ω),
    Function.Injective f → Function.Injective g → (∀ a, g (algebraMap A B a) = f a) →
    (∀ a, f a ∈ L₀) → (∀ b, g b ∈ L) →
    L₀.toSubfield ≤ Subfield.closure (Set.range f) → L.toSubfield ≤ Subfield.closure (Set.range g) →
    Module.Finite A B → Module.finrank A B = IntermediateField.relfinrank L₀ L

end GroundTheory.Heights₂.Heights.Inter
