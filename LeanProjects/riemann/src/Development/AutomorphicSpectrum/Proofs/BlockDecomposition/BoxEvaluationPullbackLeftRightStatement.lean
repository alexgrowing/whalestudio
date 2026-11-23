import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_evaluation_pullback_left_right : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (_ : dn F 1 x = 0), pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | exact GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | (intros; apply GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR <;> assumption)
