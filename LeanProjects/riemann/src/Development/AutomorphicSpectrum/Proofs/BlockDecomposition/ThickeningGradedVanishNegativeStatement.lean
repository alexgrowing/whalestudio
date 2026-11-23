import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegative
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_graded_vanish_negative : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.HU_gr_neg | exact GlobalTheory.CompanionTheory.Cone.HU_gr_neg | (intros; apply GlobalTheory.CompanionTheory.Cone.HU_gr_neg <;> assumption)
