import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordsOrigin

instance isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem one_left (X : Over (Sp R)) : (1 : X ⟶ G).left = X.hom ≫ (η[G]).left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

variable [IsCommMonObj G]

theorem tv_closedPoint (v : TanM (𝟙 (Sp R)) G) :
    (tv v).left (IsLocalRing.closedPoint (DualNumber R)) = origin G := by
  have h := congrArg (fun w => w.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  simp only [smT_left, one_left] at h
  have hl0 : IsLocalHom (epsMul (0 : R)) := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hl1 : IsLocalHom (algebraMap R (DualNumber R)) := ⟨fun a ha => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha⟩
  have e0 : (spMap (epsMul (0 : R))) (IsLocalRing.closedPoint (DualNumber R)) = IsLocalRing.closedPoint (DualNumber R) :=
    Spec_closedPoint (f := CommRingCat.ofHom (epsMul (0 : R)))
  have e1 : (spMap (algebraMap R (DualNumber R))) (IsLocalRing.closedPoint (DualNumber R)) = IsLocalRing.closedPoint R :=
    Spec_closedPoint (f := CommRingCat.ofHom (algebraMap R (DualNumber R)))
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (DualNumber R))) h
  have h3 : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) =
      (tv v).left ((spMap (epsMul (0 : R))) (IsLocalRing.closedPoint (DualNumber R))) :=
    (congrArg (fun y => (tv v).left y) e0).symm
  rw [h3]
  refine h2.trans ?_
  exact congrArg (fun y => (η[G]).left y) e1

open Classical in

def tanDer (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) : R :=
  if h : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) = origin G then
    (((G.left.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left).hom f).snd
  else 0

theorem tanDer_eq (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) :
    tanDer G v f = (((G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left).hom f).snd := by
  rw [tanDer, dif_pos (tv_closedPoint G v)]

end GlobalTheory.CoordsOrigin
