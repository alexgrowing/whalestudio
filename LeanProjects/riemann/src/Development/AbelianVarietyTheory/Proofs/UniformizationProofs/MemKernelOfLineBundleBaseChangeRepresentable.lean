import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKLIffMemKLPush
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem memKL_baseChange_rep : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  intro S S' f B _ L hL H j hrep T' x
  have h := isGrpPullback_pullback B f
  have hL' : (L.pull (pullback.fst B.hom f)).IsLB := LB.isLB_pull hL _
  rw [GlobalTheory.memKL_iff_memKL_push S S' f B _ _ L _ h hL hL' (GlobalTheory.lbIso_self hL') T' x, hrep]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.left ≫ j.left = x.left ≫ pullback.fst B.hom f := congrArg (·.left) hz
    refine ⟨Over.homMk (pullback.lift z.left T'.hom (Over.w z)) (pullback.lift_snd _ _ _), ?_⟩
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w x).symm))
    rw [← hz']
    simp [pullback.lift_fst, pullback.lift_fst_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨Over.homMk (z.left ≫ pullback.fst H.hom f) ?_, ?_⟩
    · have := Over.w z
      simp only [Over.pullback_obj_hom] at this
      simp [pullback.condition, ← this]
    · refine Over.OverMorphism.ext ?_
      change (z.left ≫ pullback.fst H.hom f) ≫ j.left = (z.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst B.hom f
      simp [pullback.lift_fst]

end GlobalTheory
