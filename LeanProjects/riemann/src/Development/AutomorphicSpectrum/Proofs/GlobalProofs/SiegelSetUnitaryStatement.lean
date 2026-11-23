import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
theorem _root_.GlobalTheory.T.siegel_set_unitary : GlobalTheory.Published.SiegelSetUnitary := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | exact GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | (intros; apply GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary <;> assumption)
