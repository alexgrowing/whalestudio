import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_ideal_eq_map : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | exact GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map <;> assumption)
