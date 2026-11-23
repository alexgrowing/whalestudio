import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_resolvent_identity : GlobalTheory.CompanionTheory.KerFc.PhiRes := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.phiRes_holds | exact GlobalTheory.CompanionTheory.KerFc.phiRes_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.phiRes_holds <;> assumption)
