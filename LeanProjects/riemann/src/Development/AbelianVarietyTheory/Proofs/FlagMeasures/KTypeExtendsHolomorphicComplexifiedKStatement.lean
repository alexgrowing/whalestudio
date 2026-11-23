import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_extends_holomorphic_complexifiedK : TauExists := by
  first | exact @GlobalTheory.Dec.TauExt.tauExists | exact GlobalTheory.Dec.TauExt.tauExists | (intros; apply GlobalTheory.Dec.TauExt.tauExists <;> assumption)
