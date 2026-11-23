import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_group_unimodular : PositivityTheory.RgBcC.Unimod := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.unimod | exact GlobalTheory.CompanionTheory.GLUnimod.unimod | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.unimod <;> assumption)
