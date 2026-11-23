import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_compact : PositivityTheory.RgBcC.VC.LgCpt := by
  first | exact @GlobalTheory.CompanionTheory.LgBound.lgCpt | exact GlobalTheory.CompanionTheory.LgBound.lgCpt | (intros; apply GlobalTheory.CompanionTheory.LgBound.lgCpt <;> assumption)
