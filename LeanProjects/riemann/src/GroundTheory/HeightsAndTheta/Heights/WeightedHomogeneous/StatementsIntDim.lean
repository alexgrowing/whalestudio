import Mathlib

namespace GroundTheory.Heights₂.Heights

noncomputable section

def IntDomainDim.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℤ A] [IsDomain A] [Algebra.FiniteType ℤ A],
    Function.Injective (algebraMap ℤ A) →
      ringKrullDim A = (((Algebra.trdeg ℤ A).toENat + 1 : ℕ∞) : WithBot ℕ∞)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights
