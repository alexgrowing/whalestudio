import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_solution_existence : PositivityTheory.RgBcC.AsmEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveAll.asmEx | exact GlobalTheory.CompanionTheory.WaveAll.asmEx | (intros; apply GlobalTheory.CompanionTheory.WaveAll.asmEx <;> assumption)
