import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

noncomputable section

instance sqfField_fact_noRoot (d : ℕ) [NeZero d] : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by
    have hd : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    rw [zero_mul, add_zero] at h
    nlinarith [sq_nonneg r]⟩

abbrev SqfField (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0

instance (d : ℕ) [NeZero d] : NumberField (SqfField d) := {}

instance (d : ℕ) [NeZero d] : Algebra.IsQuadraticExtension ℚ (SqfField d) :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

def sqrtNegD (d : ℕ) : SqfField d := ⟨0, 1⟩

end

end GroundTheory.Heights₂.Heights.Rows
