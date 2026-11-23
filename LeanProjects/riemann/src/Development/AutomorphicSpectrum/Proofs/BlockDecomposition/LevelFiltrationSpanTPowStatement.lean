import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_filtration_span_t_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | exact GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | (intros; apply GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow <;> assumption)
