import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_descent_estimate : DesPol := by
  first | exact @GlobalTheory.BigTop.Fun.desPol | exact GlobalTheory.BigTop.Fun.desPol | (intros; apply GlobalTheory.BigTop.Fun.desPol <;> assumption)
