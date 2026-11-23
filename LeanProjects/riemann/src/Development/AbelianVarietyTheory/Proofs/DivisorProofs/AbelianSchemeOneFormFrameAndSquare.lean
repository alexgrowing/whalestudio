import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem smoothOfRelativeDimension_sq {R : Type} [CommRing R] {A : Over (Sp R)} {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem basic_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧
      IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  intro R _ A _ g hA hg
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  refine ⟨GlobalTheory.T.hasGlobalOneFormFrame_of_smooth_groupScheme R A hs, ?_, AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, smoothOfRelativeDimension_sq hg⟩
  have hsq : IsPullback (𝟙 A.left) A.hom A.hom (spMap (algebraMap R R)) := by
    rw [Algebra.algebraMap_self, spMap_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA R A.left A.hom (𝟙 _) hsq

end GlobalTheory.AbCoh
