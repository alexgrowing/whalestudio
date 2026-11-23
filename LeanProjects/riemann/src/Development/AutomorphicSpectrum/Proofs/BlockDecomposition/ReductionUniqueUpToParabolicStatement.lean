import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_unique_up_to_parabolic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | exact GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | (intros; apply GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique <;> assumption)
