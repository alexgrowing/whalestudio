import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_exists : UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.UnifFix.unifEx | exact GlobalTheory.CompanionTheory.UnifFix.unifEx | (intros; apply GlobalTheory.CompanionTheory.UnifFix.unifEx <;> assumption)
