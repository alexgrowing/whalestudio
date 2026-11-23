import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_twist_identity : ThTwist := by
  first | exact @GlobalTheory.CompanionTheory.ThTw.thTwist | exact GlobalTheory.CompanionTheory.ThTw.thTwist | (intros; apply GlobalTheory.CompanionTheory.ThTw.thTwist <;> assumption)
