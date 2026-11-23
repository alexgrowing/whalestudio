import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeNoSecondWeights
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_no_second_weights : PositivityTheory.RgBcC.RealD.ConeWeightsNotSecondType := by
  first | exact @GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | exact GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | (intros; apply GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second <;> assumption)
