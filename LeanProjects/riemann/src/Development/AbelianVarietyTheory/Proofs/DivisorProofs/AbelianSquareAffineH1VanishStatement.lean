import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_square_affine_h1_vanish : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  first | exact @GlobalTheory.Obs.sq_abelian_and_affine_H1 | exact GlobalTheory.Obs.sq_abelian_and_affine_H1 | (intros; apply GlobalTheory.Obs.sq_abelian_and_affine_H1 <;> assumption)
