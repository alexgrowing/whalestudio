import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_mem_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l), Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCris.cris_in | exact GlobalTheory.CompanionTheory.LatCris.cris_in | (intros; apply GlobalTheory.CompanionTheory.LatCris.cris_in <;> assumption)
