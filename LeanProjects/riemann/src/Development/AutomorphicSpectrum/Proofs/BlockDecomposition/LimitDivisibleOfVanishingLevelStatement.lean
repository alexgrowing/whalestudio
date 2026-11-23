import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_divisible_of_vanishing_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  first | exact @GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | exact GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | (intros; apply GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul <;> assumption)
