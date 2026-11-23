import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_identity : ∀ (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ l : BC F F, ∀ T b, l.α T b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.bc_self | exact GlobalTheory.CompanionTheory.PerfVB.bc_self | (intros; apply GlobalTheory.CompanionTheory.PerfVB.bc_self <;> assumption)
