import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelFrobGrp

open GlobalTheory.AbDual GlobalTheory.PDiv

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem main : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  intro p _ R _ hR A A₁ _ _ π hπ
  have mF := frobMor p R hR A (cast_left p R hR A)
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  refine ⟨F, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, hF⟩
  have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
  exact congrArg (fun z ↦ z.left) e

end GlobalTheory.RelFrobGrp
