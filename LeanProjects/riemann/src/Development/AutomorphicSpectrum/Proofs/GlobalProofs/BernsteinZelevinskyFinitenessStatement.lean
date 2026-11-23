import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_finiteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  first | exact @GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | exact GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | (intros; apply GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness <;> assumption)
