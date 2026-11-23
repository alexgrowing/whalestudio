import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolume
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume : VolBall → PowInt := by
  first | exact @GlobalTheory.SepReal.powInt_of_volBall | exact GlobalTheory.SepReal.powInt_of_volBall | (intros; apply GlobalTheory.SepReal.powInt_of_volBall <;> assumption)
