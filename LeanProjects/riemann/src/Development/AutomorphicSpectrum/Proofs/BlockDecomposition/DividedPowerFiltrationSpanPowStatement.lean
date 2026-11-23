import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_filtration_span_pow : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ), pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | exact GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | (intros; apply GlobalTheory.CompanionTheory.DPFiltration.pdP_γB <;> assumption)
