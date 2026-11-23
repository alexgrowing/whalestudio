import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff_comp (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x = Chart.spMap (Chart.scaleD a) ≫ v := by
  rw [Chart.isLieComb_iff]
  simp [Chart.prodPts]

theorem isLieComb_one_iff (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left := by
  rw [isLieComb_one_iff_comp]
  exact ⟨fun h => by rw [h]; rfl, fun h => Over.OverMorphism.ext h⟩

theorem scale_add {v : epsR R ⟶ G} (hv : IsTangent v) (a b : R) :
    Chart.spMap (Chart.scaleD (a + b)) ≫ v =
      (Chart.spMap (Chart.scaleD a) ≫ v) * (Chart.spMap (Chart.scaleD b) ≫ v) := by
  rw [SqZero.scaleD_eq, SqZero.scaleD_eq, SqZero.scaleD_eq,
    ← SqZero.epsTo_add_comp ((Chart.isTan_iff _).2 hv) _ _ _ _ (TrivSqZeroExt.inr_mul_inr _ _ _)
      (by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  congr 3
  exact TrivSqZeroExt.inr_add _ _ _

theorem scaleD_comp (a b : R) : (Chart.scaleD a).comp (Chart.scaleD b) = Chart.scaleD (a * b) := by
  rw [SqZero.scaleD_eq a, SqZero.epsTo_comp_scaleD, SqZero.scaleD_eq]
  congr 1
  rw [← TrivSqZeroExt.inr_smul, smul_eq_mul, _root_.mul_comm]

theorem scaleD_one : Chart.scaleD (1 : R) = AlgHom.id R _ :=
  DualNumber.algHom_ext (by rw [SqZero.scaleD_eq, SqZero.epsTo_eps]; rfl)

theorem lieMultiple_calculus : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (v x y : epsR R ⟶ G) (a b : R), (IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left) ∧ (IsTangent v → IsLieComb ![a] ![v] x → IsLieComb ![b] ![v] y → IsLieComb ![a + b] ![v] (x * y)) ∧ (IsLieComb ![b] ![v] x → IsLieComb ![a] ![x] y → IsLieComb ![a * b] ![v] y) ∧ (∀ f : G ⟶ G', IsLieComb ![a] ![v] x → IsLieComb ![a] ![v ≫ f] (x ≫ f)) ∧ IsLieComb ![1] ![v] v ∧ (IsTangent v → IsLieComb ![0] ![v] 1) := by
  intro R _ G G' _ _ v x y a b
  refine ⟨isLieComb_one_iff a v x, fun hv hx hy => ?_, fun hx hy => ?_, fun f hx => ?_, ?_, fun hv => ?_⟩
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hx, hy]
    exact (scale_add hv a b).symm
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hy, hx, ← scaleD_comp, ← Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm
  · rw [isLieComb_one_iff_comp] at hx ⊢
    rw [hx]
    exact Category.assoc _ _ _
  · rw [isLieComb_one_iff_comp, scaleD_one, Chart.spMap_id]
    exact (Category.id_comp _).symm
  · rw [isLieComb_one_iff_comp, SqZero.scaleD_eq]
    exact (SqZero.epsTo_zero_comp ((Chart.isTan_iff _).2 hv) _ (TrivSqZeroExt.inr_zero _) _).symm

end GlobalTheory.LieMultiple
