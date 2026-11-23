import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_bound_integers : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K), Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | exact GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub <;> assumption)
