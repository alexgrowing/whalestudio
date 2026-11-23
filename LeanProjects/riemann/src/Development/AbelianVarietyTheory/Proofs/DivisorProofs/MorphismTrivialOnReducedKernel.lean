import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelKill

theorem comp_eq_one_of_kill_closedPoints : ∀ (A Y Y' Z : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y')
    (i : Z ⟶ A), IsPullback i (toUnit Z) u η[Y] → ∀ [AlgebraicGeometry.IsReduced Z.left] [LocallyOfFiniteType Z.hom],
    (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  intro A Y Y' Z _ _ _ _ u f i hk _ _ h T x hx
  have hiu : i ≫ u = 1 := hk.w
  have key : i ≫ f = 1 := by
    refine Over.OverMorphism.ext ?_
    have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
    refine ext_of_fromSpecResidueField_eq _ _ Y'.hom (closedPoints Z.left) ?_ (fun z hz => ?_)
      ((Over.w _).trans (Over.w _).symm)
    · rw [dense_iff_closure_eq, closure_closedPoints]
    · have hz' : IsClosed ({z} : Set Z.left) := hz
      let q : 𝟙_ (Over (Sp ℂ)) ⟶ Z :=
        Over.homMk (pointOfClosedPoint Z.hom z hz') (pointOfClosedPoint_comp _ _ _)
      have hq : q ≫ i ≫ f = q ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        apply h
        rw [Category.assoc, hiu, MonObj.comp_one]
      have e := congrArg CommaMorphism.left hq
      simp only [Over.comp_left] at e
      have hp : Z.left.fromSpecResidueField z =
          Spec.map (residueFieldIsoBase Z.hom z hz').inv ≫ pointOfClosedPoint Z.hom z hz' := by
        simp only [pointOfClosedPoint, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id,
          Category.id_comp]
      rw [hp, Category.assoc, Category.assoc]
      congr 1
  have hx' : x ≫ u = toUnit T ≫ η[Y] := hx
  rw [← hk.lift_fst x (toUnit T) hx', Category.assoc, key, MonObj.comp_one]

end GlobalTheory.KernelKill
