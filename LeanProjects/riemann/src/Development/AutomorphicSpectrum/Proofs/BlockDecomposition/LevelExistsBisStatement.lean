import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exists_bis : LevelEx := by
  first | exact @GlobalTheory.CompanionTheory.LevelU.levelEx | exact GlobalTheory.CompanionTheory.LevelU.levelEx | (intros; apply GlobalTheory.CompanionTheory.LevelU.levelEx <;> assumption)
