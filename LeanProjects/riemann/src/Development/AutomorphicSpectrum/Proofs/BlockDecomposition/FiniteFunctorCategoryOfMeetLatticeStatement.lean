import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_functor_category_of_meet_lattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ), Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | exact GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | (intros; apply GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice <;> assumption)
