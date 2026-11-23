import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_stalkMap {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    gm r z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm (𝟙 X) (r z) U a) := by
  apply Units.ext
  rw [gm_val r z U h, Units.coe_map, gm_val (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a.val).symm

theorem pull_isLB_of_isOn : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) →
    (L.pull r).IsLB := by
  intro X Z W L r hL hr
  have coc : ∀ (z : Z) (a b c : L.ι), r z ∈ L.U a → r z ∈ L.U b → r z ∈ L.U c →
      gm r z _ (L.g a b) * gm r z _ (L.g b c) = gm r z _ (L.g a c) := by
    intro z a b c ha hb hc
    rw [gm_eq_stalkMap r z (L.U a ⊓ L.U b) ⟨ha, hb⟩, gm_eq_stalkMap r z (L.U b ⊓ L.U c) ⟨hb, hc⟩,
      gm_eq_stalkMap r z (L.U a ⊓ L.U c) ⟨ha, hc⟩, ← map_mul,
      hL.coc (r z) a b c ha hb hc]
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    obtain ⟨a, ha⟩ := hL.cov (r z) (hr z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => a, mem_pull.2 ha⟩
  · intro J
    refine unit_ext fun z hz => ?_
    rw [gm_res (𝟙 Z) z _ hz, map_one, gm_pull_g L r (𝟙 Z) z J J hz hz, Category.id_comp]
    have hJ := mem_pull.1 hz
    exact mul_eq_left.1 (coc z _ _ _ hJ hJ hJ)
  · intro I J K
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_pull_g L r (𝟙 Z) z I J hz.1.1 hz.1.2,
      gm_pull_g L r (𝟙 Z) z J K hz.1.2 hz.2, gm_pull_g L r (𝟙 Z) z I K hz.1.1 hz.2, Category.id_comp]
    exact coc z _ _ _ (mem_pull.1 hz.1.1) (mem_pull.1 hz.1.2) (mem_pull.1 hz.2)

end GlobalTheory.PicGlue
