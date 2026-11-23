import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitUniversal_eq_pullback_box_evaluation : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n), UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.UU_evF | exact GlobalTheory.CompanionTheory.HopfC.UU_evF | (intros; apply GlobalTheory.CompanionTheory.HopfC.UU_evF <;> assumption)
