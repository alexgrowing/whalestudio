import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChange
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisting_sheaf_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R) (D : E.LineData X), IsTautologicalLine p D → IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback | exact GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback <;> assumption)
