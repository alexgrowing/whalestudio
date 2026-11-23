import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzExistsRealMajorant
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_exists_real_majorant : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ), ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  first | exact @GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | exact GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | (intros; apply GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant <;> assumption)
