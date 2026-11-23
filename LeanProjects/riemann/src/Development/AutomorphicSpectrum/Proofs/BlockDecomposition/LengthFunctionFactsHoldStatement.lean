import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_facts_hold : PositivityTheory.RgBcC.LgFacts := by
  first | exact @GlobalTheory.CompanionTheory.LengthGL.lgFacts | exact GlobalTheory.CompanionTheory.LengthGL.lgFacts | (intros; apply GlobalTheory.CompanionTheory.LengthGL.lgFacts <;> assumption)
