import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_dim_eq_relative_dim : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  first | exact @GlobalTheory.CompanionTheory.CoordCard.main | exact GlobalTheory.CompanionTheory.CoordCard.main | (intros; apply GlobalTheory.CompanionTheory.CoordCard.main <;> assumption)
