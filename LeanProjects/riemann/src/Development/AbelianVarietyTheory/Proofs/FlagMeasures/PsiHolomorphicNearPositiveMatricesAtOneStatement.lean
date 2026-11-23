import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one : PsBasic := by
  first | exact @GlobalTheory.Dec.psBasic | exact GlobalTheory.Dec.psBasic | (intros; apply GlobalTheory.Dec.psBasic <;> assumption)
