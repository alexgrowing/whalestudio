import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomogeneousFormSectionsEqZeroOfThickenings
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 := by
  first | exact @GlobalTheory.FormVan.form_eq_zero | exact GlobalTheory.FormVan.form_eq_zero | (intros; apply GlobalTheory.FormVan.form_eq_zero <;> assumption)
