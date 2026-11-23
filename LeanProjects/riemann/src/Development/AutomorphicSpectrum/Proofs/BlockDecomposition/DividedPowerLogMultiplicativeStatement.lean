import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicative
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_log_multiplicative : ∀ {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ),
    (∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) → ∀ v w : A, v - 1 ∈ J → w - 1 ∈ J →
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  first | exact @GlobalTheory.CompanionTheory.TruncLog.dlog_mul | exact GlobalTheory.CompanionTheory.TruncLog.dlog_mul | (intros; apply GlobalTheory.CompanionTheory.TruncLog.dlog_mul <;> assumption)
