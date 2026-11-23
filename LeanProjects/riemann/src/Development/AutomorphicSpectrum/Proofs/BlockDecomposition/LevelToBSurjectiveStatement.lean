import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_surjective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), Function.Surjective (lev h k).toB := by
  first | exact @GlobalTheory.CompanionTheory.LatLevels.toB_surjective | exact GlobalTheory.CompanionTheory.LatLevels.toB_surjective | (intros; apply GlobalTheory.CompanionTheory.LatLevels.toB_surjective <;> assumption)
