import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

set_option backward.isDefEq.respectTransparency false in

theorem stalkClosedPointTo_localMap_comp {X : Scheme.{0}} {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B]
    (x : Spec A ⟶ X) (g : A ⟶ B) [IsLocalHom g.hom] (y : Spec B ⟶ X) (hy : y = Spec.map g ≫ x) (x₀ : X)
    (h₁ : x (IsLocalRing.closedPoint A) = x₀) (h₂ : y (IsLocalRing.closedPoint B) = x₀) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo y =
      ((X.presheaf.stalkCongr (Inseparable.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo x) ≫ g := by
  subst h₁
  have hy' : y = Spec.map (Scheme.stalkClosedPointTo x ≫ g) ≫ X.fromSpecStalk _ := by
    rw [hy, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  clear hy
  subst hy'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo x ≫ g).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo x ≫ g) U _

theorem tanDer_smul : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  intro R _ _ G _ _ r v f
  have hl : IsLocalHom (CommRingCat.ofHom (epsMul r)).hom := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hy : (tv (r • v)).left = Spec.map (CommRingCat.ofHom (epsMul r)) ≫ (tv v).left := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left]
  have key := stalkClosedPointTo_localMap_comp (A := CommRingCat.of (DualNumber R)) (B := CommRingCat.of (DualNumber R))
    (tv v).left (CommRingCat.ofHom (epsMul r)) (tv (r • v)).left hy (origin G) (tv_closedPoint G v)
    (tv_closedPoint G (r • v))
  rw [tanDer_eq, tanDer_eq]
  refine (congrArg (fun φ => (φ.hom f).snd) key).trans ?_
  have hs : ∀ a : DualNumber R, (epsMul r a).snd = r * a.snd := fun a => by simp [epsMul]
  exact hs _

end GlobalTheory.CoordsOrigin
