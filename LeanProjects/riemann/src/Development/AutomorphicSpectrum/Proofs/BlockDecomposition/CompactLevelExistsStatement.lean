import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_level_exists : KEx := by
  first | exact @GlobalTheory.CompanionTheory.KExLevel.kEx | exact GlobalTheory.CompanionTheory.KExLevel.kEx | (intros; apply GlobalTheory.CompanionTheory.KExLevel.kEx <;> assumption)
