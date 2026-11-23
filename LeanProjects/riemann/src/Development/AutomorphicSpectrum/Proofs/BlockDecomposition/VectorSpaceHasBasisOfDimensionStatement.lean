import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_space_has_basis_of_dimension : ∀ {R : Type} [CommRing R] (_ : IsField R) {M : Type} [AddCommGroup M] [Module R M] (g : ℕ), VB R M g → Nonempty (Module.Basis (Fin g) R M) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | exact GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | (intros; apply GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField <;> assumption)
