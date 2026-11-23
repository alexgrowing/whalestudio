import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def IntClosureLocFinite.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (S : Finset L), Subfield.closure (S : Set L) = ⊤ →
    ∀ (A : Subring F) (T : Finset F), Subring.closure (T : Set F) ≤ A →
    (∀ z ∈ A, ∃ b ∈ Subring.closure (T : Set F), ∃ c ∈ Subring.closure (T : Set F),
      c ≠ 0 ∧ c⁻¹ ∈ A ∧ z * c = b) →
    letI := (φ.comp A.subtype).toAlgebra
    letI : Module A L := Algebra.toModule
    ∃ t : Finset L, ∀ x : L, IsIntegral A x → x ∈ Submodule.span A (t : Set L)

end GroundTheory.Heights₂.Heights.Inter
