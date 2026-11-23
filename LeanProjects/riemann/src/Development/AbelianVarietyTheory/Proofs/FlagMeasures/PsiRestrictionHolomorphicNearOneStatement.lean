import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_restriction_holomorphic_near_one : PsLocal := by
  first | exact @GlobalTheory.Dec.psLocal | exact GlobalTheory.Dec.psLocal | (intros; apply GlobalTheory.Dec.psLocal <;> assumption)
