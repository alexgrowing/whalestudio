import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.T

open Matrix

def TJTrev : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (q d di : A) (Y : R),
    d * di = 1 → di * d = 1 → d * q = q * d + d →
      Tm (Y + 1) q d di * J A * (Tm Y q d di)ᵀ = J A

end Formalism.YangianSpanCharacter.T
