import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_lattice_dpow_closed : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  first | exact @GlobalTheory.CompanionTheory.LatCHc.hc_k | exact GlobalTheory.CompanionTheory.LatCHc.hc_k | (intros; apply GlobalTheory.CompanionTheory.LatCHc.hc_k <;> assumption)
