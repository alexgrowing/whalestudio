import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def ConstantsDescend.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω), R.FG → Module.Finite ℤ T →
    (∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom) →
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t ∈ T, (m : Ω) * t ∈ R

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
