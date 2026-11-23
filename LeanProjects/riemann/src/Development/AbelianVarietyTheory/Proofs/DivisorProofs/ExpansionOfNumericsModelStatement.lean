import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_of_numerics_model : Formalism.CohomologicalDescent.E.ExCut → NumSt → SumExpSt → ModelSt → ExpSt := by
  first | exact @GlobalTheory.ExpTie.Asm.expSt_of | exact GlobalTheory.ExpTie.Asm.expSt_of | (intros; apply GlobalTheory.ExpTie.Asm.expSt_of <;> assumption)
