import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_fixes_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : K), (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | exact GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K <;> assumption)
