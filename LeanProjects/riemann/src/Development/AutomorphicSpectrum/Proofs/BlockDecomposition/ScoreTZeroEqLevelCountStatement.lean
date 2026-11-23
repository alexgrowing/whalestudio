import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCount
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.score_tZero_eq_level_count : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n, score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.score_tZero_level | exact GlobalTheory.CompanionTheory.CoefId.score_tZero_level | (intros; apply GlobalTheory.CompanionTheory.CoefId.score_tZero_level <;> assumption)
