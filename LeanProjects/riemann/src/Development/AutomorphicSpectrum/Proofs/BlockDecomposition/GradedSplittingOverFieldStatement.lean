import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_over_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  first | exact @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | exact GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit <;> assumption)
