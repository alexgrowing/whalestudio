import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_coboundary_formula : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn | exact GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn | (intros; apply GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn <;> assumption)
