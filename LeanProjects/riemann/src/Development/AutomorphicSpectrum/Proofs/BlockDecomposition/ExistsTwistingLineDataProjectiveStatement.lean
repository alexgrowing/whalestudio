import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjective
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisting_line_data_projective : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N), ∃ D : E.LineData X, IsTautologicalLineAt D N i := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | exact GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main <;> assumption)
