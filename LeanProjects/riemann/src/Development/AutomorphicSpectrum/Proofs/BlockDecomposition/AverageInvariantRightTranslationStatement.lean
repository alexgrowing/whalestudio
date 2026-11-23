import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariant_right_translation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | exact GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant <;> assumption)
