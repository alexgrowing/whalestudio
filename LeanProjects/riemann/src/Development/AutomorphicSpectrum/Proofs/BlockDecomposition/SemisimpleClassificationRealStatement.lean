import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_classification_real : PositivityTheory.RgBcC.RealD.SemiCls := by
  first | exact @GlobalTheory.CompanionTheory.SemiClass.semiCls | exact GlobalTheory.CompanionTheory.SemiClass.semiCls | (intros; apply GlobalTheory.CompanionTheory.SemiClass.semiCls <;> assumption)
