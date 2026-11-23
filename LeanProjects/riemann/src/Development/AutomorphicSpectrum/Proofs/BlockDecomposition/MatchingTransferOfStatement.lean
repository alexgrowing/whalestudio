import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_transfer_of : MatchTOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPow.matchTOf | exact GlobalTheory.CompanionTheory.MatchPow.matchTOf | (intros; apply GlobalTheory.CompanionTheory.MatchPow.matchTOf <;> assumption)
