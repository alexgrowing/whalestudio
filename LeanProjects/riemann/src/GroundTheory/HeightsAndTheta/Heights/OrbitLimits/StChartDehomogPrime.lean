import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ChartDehomogPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime W → linForm t ∉ W → (W ⊔ Ideal.span {linForm t - 1}).IsPrime

end GroundTheory.Heights₂.Heights
