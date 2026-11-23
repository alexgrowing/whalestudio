import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_identity_statement : RightId := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.rightId | exact GlobalTheory.CompanionTheory.Dblock.rightId | (intros; apply GlobalTheory.CompanionTheory.Dblock.rightId <;> assumption)
