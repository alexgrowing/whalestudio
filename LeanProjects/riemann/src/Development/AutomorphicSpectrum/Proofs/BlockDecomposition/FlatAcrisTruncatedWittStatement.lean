import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
