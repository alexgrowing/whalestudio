import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | exact GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main <;> assumption)
