import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_exists : SplitEx := by
  first | exact @GlobalTheory.CompanionTheory.SplitLevel.splitEx | exact GlobalTheory.CompanionTheory.SplitLevel.splitEx | (intros; apply GlobalTheory.CompanionTheory.SplitLevel.splitEx <;> assumption)
