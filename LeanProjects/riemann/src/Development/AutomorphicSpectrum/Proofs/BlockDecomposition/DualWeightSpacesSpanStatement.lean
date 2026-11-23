import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpan
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weight_spaces_span : ∀ {n : ℕ} (E : KMod n), (⨆ μ, wtDual E μ) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | exact GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top <;> assumption)
