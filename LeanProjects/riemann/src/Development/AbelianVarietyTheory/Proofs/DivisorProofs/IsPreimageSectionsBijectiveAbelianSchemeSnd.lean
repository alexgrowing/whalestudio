import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_app_iso_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (V : Z.Opens)
    (h : Function.Bijective (g.app V).hom) : Function.Bijective ((f ≫ g).app V).hom := by
  have : IsIso (g.app V) := (ConcreteCategory.isIso_iff_bijective _).2 h
  have : IsIso (f.app (g ⁻¹ᵁ V)) := inferInstance
  have : IsIso ((f ≫ g).app V) := by
    rw [Scheme.Hom.comp_app]; exact IsIso.comp_isIso' ‹_› ‹_›
  exact ConcreteCategory.bijective_of_isIso _

theorem fnBij_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  intro S A T _ hA V
  have e : (snd A T).left = (β_ A T).hom.left ≫ (fst T A).left := by
    rw [← Over.comp_left, braiding_hom_fst]
  have : IsIso (β_ A T).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ A T).hom))
  rw [e]
  exact bijective_app_iso_comp _ _ V
    (GlobalTheory.CubeLawCompare.bijective_app_fst GlobalTheory.SemiRigid.globalFns hA T V)

end GlobalTheory.PicGlue
