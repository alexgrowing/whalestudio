import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryDegreeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_coboundary_degree_zero : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (v : Cn (box F) 0), Sh F 0 (dn (box F) 0 v) = prA F (dl 0) (S0 F 0 v) - prA F (dl 1) (S0 F 0 v) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero | exact GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero | (intros; apply GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero <;> assumption)
