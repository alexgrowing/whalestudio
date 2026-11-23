import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coordinate_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), ∀ k : Fin d, IsUnit (tV i y hy V hV k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | exact GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | (intros; apply GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit <;> assumption)
