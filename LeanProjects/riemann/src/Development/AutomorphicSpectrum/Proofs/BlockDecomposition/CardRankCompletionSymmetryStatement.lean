import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rank_completion_symmetry : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | exact GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | (intros; apply GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm <;> assumption)
