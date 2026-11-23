import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinCocyclesDegreeZeroAreConstants
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stein_cocycles_degree_zero_are_constants : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), Stein F → (∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0)) ∧ ∀ r : R, r • (1 : Cn F 0) = 0 → r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.stein_cn | exact GlobalTheory.CompanionTheory.HopfC.stein_cn | (intros; apply GlobalTheory.CompanionTheory.HopfC.stein_cn <;> assumption)
