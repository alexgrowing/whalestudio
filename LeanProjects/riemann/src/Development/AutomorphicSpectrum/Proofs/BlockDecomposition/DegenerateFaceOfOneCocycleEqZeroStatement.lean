import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerate_face_of_one_cocycle_eq_zero : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1) (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate | exact GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate | (intros; apply GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate <;> assumption)
