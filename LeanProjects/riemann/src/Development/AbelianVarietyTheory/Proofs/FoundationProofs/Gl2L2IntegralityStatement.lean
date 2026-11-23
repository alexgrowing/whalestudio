import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gl2L2Integrality
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2a2_integral_bound_of_sums : Formalism.HermitianLattices.GL2a2.PartialSumIntegralBound := by
  first | exact @GlobalTheory.PsiTail.psi_tail_bound | exact GlobalTheory.PsiTail.psi_tail_bound | (intros; apply GlobalTheory.PsiTail.psi_tail_bound <;> assumption)
