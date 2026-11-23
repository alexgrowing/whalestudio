import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_square_congruence_conjugation : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | exact GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | (intros; apply GlobalTheory.CompanionTheory.Jp.Twist.twist_gam <;> assumption)
