import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_constant_term_bound : PcBound := by
  first | exact @GlobalTheory.CompanionTheory.PcB.pcBound | exact GlobalTheory.CompanionTheory.PcB.pcBound | (intros; apply GlobalTheory.CompanionTheory.PcB.pcBound <;> assumption)
