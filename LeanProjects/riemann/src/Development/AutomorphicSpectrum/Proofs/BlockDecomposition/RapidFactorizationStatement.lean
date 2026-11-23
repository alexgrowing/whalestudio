import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapid_factorization : GlobalTheory.CompanionTheory.KerFc.FactorRapid := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.factorRapid | exact GlobalTheory.CompanionTheory.KerFc.factorRapid | (intros; apply GlobalTheory.CompanionTheory.KerFc.factorRapid <;> assumption)
