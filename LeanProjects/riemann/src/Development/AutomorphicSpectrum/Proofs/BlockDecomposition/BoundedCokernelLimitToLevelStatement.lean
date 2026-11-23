import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_cokernel_limit_to_level : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim → ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  first | exact @GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | exact GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | (intros; apply GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded <;> assumption)
