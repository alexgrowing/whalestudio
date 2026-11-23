import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

theorem isUnit_of_isUnit_appTop_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (a : Γ(Y, ⊤)) (h : IsUnit (f.appTop a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ X.basicOpen (f.appTop a) := by
    rw [Scheme.basicOpen_of_isUnit _ h]; trivial
  rw [← Scheme.preimage_basicOpen_top] at hx
  exact (Y.mem_basicOpen _ _ (by trivial)).1 hx

theorem units_lift_of_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left →
      Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  intro S A _ hA T₂ T₀ k _ _ _ u
  have hb₀ : Function.Bijective (snd A T₀).left.appTop.hom :=
    CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA (IsPullback.of_hasPullback A.hom T₀.hom)
  have hk : Function.Surjective k.left.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine k.left).2
  have hc : (A ◁ k).left ≫ (snd A T₂).left = (snd A T₀).left ≫ k.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hc' : ∀ w, (A ◁ k).left.appTop ((snd A T₂).left.appTop w) =
      (snd A T₀).left.appTop (k.left.appTop w) := by
    intro w
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hc]
  obtain ⟨v, hv⟩ := hb₀.2 (u : Γ((A ⊗ T₀).left, ⊤))
  obtain ⟨w, rfl⟩ := hk v
  let e := RingEquiv.ofBijective (snd A T₀).left.appTop.hom hb₀
  have hvu : IsUnit (k.left.appTop w) := by
    have : IsUnit (e (k.left.appTop w)) := by
      show IsUnit ((snd A T₀).left.appTop (k.left.appTop w)); rw [hv]; exact u.isUnit
    exact (isUnit_map_iff e _).1 this
  have hw : IsUnit w := isUnit_of_isUnit_appTop_of_surjective k.left w hvu
  obtain ⟨w', hw'⟩ := hw.map (snd A T₂).left.appTop.hom
  refine ⟨w', Units.ext ?_⟩
  show (A ◁ k).left.appTop (w' : Γ((A ⊗ T₂).left, ⊤)) = u
  rw [hw', hc', hv]

end GlobalTheory.DualOpen
