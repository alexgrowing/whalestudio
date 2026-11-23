import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 2 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I →
        chowDegree I (e + 2) = (divCycle I u).sum fun W m => m * chowDegree W (e + 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
