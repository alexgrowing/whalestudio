import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSndStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem eq_zero_of_rigid_of_locally_zero : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 →
      (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
        GlobalTheory.CechPic.pull (A ◁ z).left c = 0) → c = 0 := by
  intro S A T _ hA c h₀ loc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hf := GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA
  refine (cls_eq_zero_iff hL).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hL (snd A T).left
    (lift (1 : T ⟶ A) (𝟙 T)).left ?_ (GlobalTheory.CubeGlue.surjective_restrict _ fun V ↦ ?_)
    ((cls_eq_zero_iff (pull_isLB hL _)).1 h₀) fun p ↦ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hf V)
  · obtain ⟨Z, z, hz, hp, h⟩ := loc p
    obtain ⟨hw, hr⟩ := GlobalTheory.whiskerLeft_isOpenImmersion_range S A T Z z hz
    refine ⟨z.left.opensRange, hp, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    obtain ⟨m, hm⟩ : ∃ m : ((snd A T).left ⁻¹ᵁ z.left.opensRange).toScheme ⟶ (A ⊗ Z).left,
        m ≫ (A ◁ z).left = ((snd A T).left ⁻¹ᵁ z.left.opensRange).ι :=
      ⟨IsOpenImmersion.lift _ _ (by
        rw [Scheme.Opens.range_ι]
        exact fun x hx ↦ (hr x).2 hx), IsOpenImmersion.lift_fac _ _ _⟩
    rw [cls_pull hL, ← hm, pull_comp, h, map_zero]

end GlobalTheory.PicGlue
