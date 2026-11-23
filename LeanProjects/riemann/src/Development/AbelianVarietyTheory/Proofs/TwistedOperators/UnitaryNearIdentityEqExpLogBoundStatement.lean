import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryNearIdentityEqExpLogBound
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_near_identity_eq_exp_log_bound : LogNear := by
  first | exact @GlobalTheory.SepReal.logNear_holds | exact GlobalTheory.SepReal.logNear_holds | (intros; apply GlobalTheory.SepReal.logNear_holds <;> assumption)
