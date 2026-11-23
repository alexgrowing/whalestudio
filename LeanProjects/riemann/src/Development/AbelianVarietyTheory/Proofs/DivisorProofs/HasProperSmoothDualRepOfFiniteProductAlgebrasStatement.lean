import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebras
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | exact GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | (intros; apply GlobalTheory.DualCon.ProdGlue.hasRepAF_pi <;> assumption)
