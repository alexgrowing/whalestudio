import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubQuotientStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags.main | exact GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags.main <;> assumption)
