import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_finiteType : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}, IsAffineOpen W → letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first | exact @GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | exact GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | (intros; apply GlobalTheory.CompanionTheory.GeoFT.finiteType_affine <;> assumption)
