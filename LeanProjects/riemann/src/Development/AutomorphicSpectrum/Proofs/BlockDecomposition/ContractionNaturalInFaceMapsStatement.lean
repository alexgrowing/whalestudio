import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMaps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_natural_in_face_maps : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | exact GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | (intros; apply GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr <;> assumption)
