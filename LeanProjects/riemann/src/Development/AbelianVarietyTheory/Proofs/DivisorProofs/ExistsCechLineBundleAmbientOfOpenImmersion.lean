import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem image_inf_le (a b : L.ι) : f ''ᵁ L.U a ⊓ f ''ᵁ L.U b ≤ f ''ᵁ (L.U a ⊓ L.U b) := fun x hx ↦ by
  obtain ⟨w, hw, rfl⟩ := hx.1
  exact f.apply_mem_image_iff.2 ⟨hw, f.apply_mem_image_iff.1 hx.2⟩

def extLB : LB X :=
  ⟨L.ι, fun a ↦ f ''ᵁ L.U a, fun a b ↦ res (image_inf_le f L a b) (GlobalTheory.GlueLineBundle.imU f _ (L.g a b))⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (a b : L.ι) (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gm (r ≫ f) z ((extLB f L).U a ⊓ (extLB f L).U b) ((extLB f L).g a b) = gm r z (L.U a ⊓ L.U b) (L.g a b) := by
  have hm : (r ≫ f) z ∈ f ''ᵁ L.U a ⊓ f ''ᵁ L.U b := ⟨f.apply_mem_image_iff.2 ha, f.apply_mem_image_iff.2 hb⟩
  exact (gm_res (r ≫ f) z (image_inf_le f L a b) hm _).trans
    (GlobalTheory.GlueLineBundle.gm_imU f r z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)

variable {f} in

theorem gm_eq_map {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (U : X.Opens) (h : g y ∈ U) (a : Γ(X, U)ˣ) :
    gm g y U a = Units.map (g.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (g y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val g y U h, GlobalTheory.GlueLineBundle.gm_id_val h]
  exact (Scheme.Hom.germ_stalkMap_apply g U y h a.val).symm

end GlobalTheory.PicGlue.OpenExt

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem isOn_extLB (hL : L.IsLB) : IsOn f.opensRange (extLB f L) where
  le a x hx := by
    obtain ⟨w, -, rfl⟩ := hx
    exact ⟨w, rfl⟩
  cov x hx := by
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_chart hL w
    exact ⟨a, f.apply_mem_image_iff.2 ha⟩
  coc x a b c hxa hxb hxc := by
    obtain ⟨w, ha, rfl⟩ := hxa
    have hb : w ∈ L.U b := f.apply_mem_image_iff.1 hxb
    have hc : w ∈ L.U c := f.apply_mem_image_iff.1 hxc
    have e : ∀ (d d' : L.ι) (hd : w ∈ L.U d) (hd' : w ∈ L.U d'),
        Units.map (f.stalkMap w).hom.toMonoidHom (gm (𝟙 X) (f w) _ ((extLB f L).g d d')) =
          gm (𝟙 X') w (L.U d ⊓ L.U d') (L.g d d') := by
      intro d d' hd hd'
      rw [← gm_eq_map f w ((extLB f L).U d ⊓ (extLB f L).U d') ⟨f.apply_mem_image_iff.2 hd, f.apply_mem_image_iff.2 hd'⟩]
      have k := gm_ext_g f L (𝟙 X') w d d' hd hd'
      rwa [Category.id_comp] at k
    apply Units.map_injective (f := (f.stalkMap w).hom.toMonoidHom)
      (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (f.stalkMap w)).1 h)
    refine (MonoidHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (e a b ha hb) (e b c hb hc)).trans
      ((gm_cocycle hL (𝟙 X') w ha hb hc).trans (e a c ha hc).symm)

end GlobalTheory.PicGlue.OpenExt

open GlobalTheory.PicGlue.OpenExt in

theorem GlobalTheory.PicGlue.exists_isOn_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'),
    L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  intro X X' f _ L hL
  refine ⟨extLB f L, isOn_extLB f L hL, iso_of_chart hL ⟨fun J ↦ J PUnit.unit, ?_, ?_⟩⟩
  · intro J y hy
    exact f.apply_mem_image_iff.1 (mem_pull.1 hy)
  · intro y J J' hj hj'
    exact (gm_pull_g (extLB f L) f (𝟙 X') y J J' hj hj').trans
      (gm_ext_g f L (𝟙 X') y _ _ (f.apply_mem_image_iff.1 (mem_pull.1 hj)) (f.apply_mem_image_iff.1 (mem_pull.1 hj')))
