import Mathlib

set_option autoImplicit false

namespace GlobalTheory.Published

def NormalCompletionSt : Prop :=
  ∀ (V B : Type) [CommRing V] [IsDedekindDomain V] [CharZero V] [CommRing B] [IsLocalRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra V B] [Algebra.EssFiniteType V B],
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal B) B)

end GlobalTheory.Published
