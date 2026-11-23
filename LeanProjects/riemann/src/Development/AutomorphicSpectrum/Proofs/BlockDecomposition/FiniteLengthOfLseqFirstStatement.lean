import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_of_lseq_first : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | exact GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | (intros; apply GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level <;> assumption)
