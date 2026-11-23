import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def MaximalIdealHeightFG.Statement : Prop :=
  ∀ (F : Type u) [Field F] (A : Type u) [CommRing A] [IsDomain A] [Algebra F A]
    [Algebra.FiniteType F A] (m : Ideal A), m.IsMaximal → (m.height : WithBot ℕ∞) = ringKrullDim A

section Examples

example : Algebra.FiniteType ℚ (MvPolynomial (Fin 2) ℚ) := inferInstance

example : IsDomain (MvPolynomial (Fin 2) ℚ) := inferInstance

end Examples

end GroundTheory.Heights₂.Heights.NumbersDVR
