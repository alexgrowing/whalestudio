import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_total_of_hecke_eta : HeckeEta → ThTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.thTotal | exact GlobalTheory.CompanionTheory.ThTot.thTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.thTotal <;> assumption)
