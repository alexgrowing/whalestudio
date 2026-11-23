import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapComposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_composition : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F''), ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | exact GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp <;> assumption)
