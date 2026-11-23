import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_base_change : GlobalTheory.HighWt.BaseChange := by
  first | exact @GlobalTheory.HighWt.baseChange_holds | exact GlobalTheory.HighWt.baseChange_holds | (intros; apply GlobalTheory.HighWt.baseChange_holds <;> assumption)
