import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicComplete
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_isAdicComplete_span_prime : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  first | exact @GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | exact GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | (intros; apply GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete <;> assumption)
