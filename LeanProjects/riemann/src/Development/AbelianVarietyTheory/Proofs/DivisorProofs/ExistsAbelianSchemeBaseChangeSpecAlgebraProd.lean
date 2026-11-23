import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left) (q : B'.left ⟶ (SpAlg R D ⊗ B).left), IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧ SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧ q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  refine ⟨(Over.pullback (spMap (algebraMap R D))).obj B, inferInstance, CategoryTheory.Limits.pullback.fst B.hom _,
    (CategoryTheory.Limits.pullbackSymmetry B.hom (spMap (algebraMap R D))).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B _, GlobalTheory.isAbelianScheme_pullback_obj _ B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback _ _) hg,
    inferInstance, ?_, ?_⟩
  · simp
  · simp

end GlobalTheory
