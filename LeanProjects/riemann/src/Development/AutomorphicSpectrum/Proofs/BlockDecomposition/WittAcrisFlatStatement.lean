import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_acris_flat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K), Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  first | exact @GlobalTheory.CompanionTheory.FlatW.flat_AW | exact GlobalTheory.CompanionTheory.FlatW.flat_AW | (intros; apply GlobalTheory.CompanionTheory.FlatW.flat_AW <;> assumption)
