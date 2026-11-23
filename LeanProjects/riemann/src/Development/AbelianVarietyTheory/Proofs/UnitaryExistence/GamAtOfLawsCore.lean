import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore' : ∀ (D : D7) (T : Core D), LawsCore T → GlobalTheory.RunIn.GamAt T :=
  fun D T h j hj σ hσ => GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ

end GlobalTheory.RunIn
