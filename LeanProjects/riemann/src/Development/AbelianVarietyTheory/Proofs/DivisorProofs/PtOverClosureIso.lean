import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH GlobalTheory.PushEigen
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
