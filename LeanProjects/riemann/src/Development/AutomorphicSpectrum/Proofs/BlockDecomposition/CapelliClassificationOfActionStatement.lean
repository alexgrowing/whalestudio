import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfAction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaSelfH
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_classification_of_action : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := by
  first | exact @GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | exact GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | (intros; apply GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU <;> assumption)
