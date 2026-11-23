import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_linear_in_functional : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q), Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Con_linear_form | exact GlobalTheory.CompanionTheory.HopfC.Con_linear_form | (intros; apply GlobalTheory.CompanionTheory.HopfC.Con_linear_form <;> assumption)
