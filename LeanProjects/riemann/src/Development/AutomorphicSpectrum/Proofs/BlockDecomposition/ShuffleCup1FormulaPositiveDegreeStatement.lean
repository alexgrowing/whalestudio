import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1FormulaPositiveDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_cup1_formula_positive_degree : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (u : Cn (box F) 1) (w : Cn (box F) (n + 1)), Sh F (n + 1) (cup1 (box F) (n + 1) u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst (n + 1) 1) OrderHom.id w - bv F (cst 1 0) (fr n) u * prB F (dl 0) (Sh F n w) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula | exact GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula | (intros; apply GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula <;> assumption)
