import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem nonempty_tq_pullback_comp {T S S' : Scheme.{0}} (r : T ⟶ S') (f : S' ⟶ S) {g : T ⟶ S} (h : g = r ≫ f)
    (G : Over S) [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ ((Over.pullback f).obj G) X) :
    Nonempty (TQ ((Over.pullback g).obj G) X) := by
  subst h
  obtain ⟨Q', -⟩ := exists_tq_baseChange _ _ _ X _ _ _
    ((isGrpPullback_of_iso (pullCompIso r f G)).comp (isGrpPullback_pullback _ r)) Q
  exact ⟨Q'⟩

theorem thick_zero_factor (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ r, thick V (IsLocalRing.maximalIdeal V) 0 = r ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (show IsLocalRing.maximalIdeal V ≤ IsLocalRing.maximalIdeal V ^ (0 + 1) by simp))), ?_⟩
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.UU
