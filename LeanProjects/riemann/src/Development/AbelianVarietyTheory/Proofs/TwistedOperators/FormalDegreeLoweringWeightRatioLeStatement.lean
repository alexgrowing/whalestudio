import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_loweringWeight_ratio_le : DegRatio := by
  first | exact @GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | exact GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | (intros; apply GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds <;> assumption)
