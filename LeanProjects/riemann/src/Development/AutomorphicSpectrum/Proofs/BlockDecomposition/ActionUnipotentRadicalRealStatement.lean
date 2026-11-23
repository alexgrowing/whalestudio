import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionUnipotentRadicalReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_unipotent_radical_real : PositivityTheory.RgBcC.RealD.ActUU := by
  first | exact @GlobalTheory.CompanionTheory.PairBridge.actUU | exact GlobalTheory.CompanionTheory.PairBridge.actUU | (intros; apply GlobalTheory.CompanionTheory.PairBridge.actUU <;> assumption)
