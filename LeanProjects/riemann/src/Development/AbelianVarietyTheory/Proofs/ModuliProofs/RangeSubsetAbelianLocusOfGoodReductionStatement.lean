import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_goodReduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X : Scheme.{0}) (z : X ⟶ Sp ℤ) (G : Over X) [GrpObj G] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (y : Sp V ⟶ X) (𝒜 : Over (Sp V)) [GrpObj 𝒜] (A : Over (Sp C)) [GrpObj A] (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ G.left), LocallyOfFiniteType z → IsSemiAbelian G → IsAbelianScheme 𝒜 → IsGrpPullback A 𝒜 (spMap (algebraMap V C)) φ₁ → IsGrpPullback A G (spMap (algebraMap V C) ≫ y) φ₂ → Set.range y ⊆ abLocus G := by
  first | exact @GlobalTheory.range_subset_abLocus_of_goodReduction | exact GlobalTheory.range_subset_abLocus_of_goodReduction | (intros; apply GlobalTheory.range_subset_abLocus_of_goodReduction <;> assumption)
