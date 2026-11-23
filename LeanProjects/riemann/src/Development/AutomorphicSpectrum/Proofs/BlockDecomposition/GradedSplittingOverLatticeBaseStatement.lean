import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_over_lattice_base : ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → LatBase γ l m → Nonempty (GrSplit O γ m) := by
  first | exact @GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | exact GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit <;> assumption)
