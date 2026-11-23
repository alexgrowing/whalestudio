import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_expansion_statement : SumExpSt := by
  first | exact @GlobalTheory.ExpTie.sumExpSt | exact GlobalTheory.ExpTie.sumExpSt | (intros; apply GlobalTheory.ExpTie.sumExpSt <;> assumption)
