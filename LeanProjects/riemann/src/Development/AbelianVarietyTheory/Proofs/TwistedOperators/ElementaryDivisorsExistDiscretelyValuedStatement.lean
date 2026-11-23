import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValued
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued : Smith := by
  first | exact @GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | exact GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | (intros; apply GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued <;> assumption)
