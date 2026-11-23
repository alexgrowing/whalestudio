import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PicGlue

theorem stalkMap_gm {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem rigOn_of_triv_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X),
    (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  intro X Y e V L hV ⟨t, ht⟩
  have hle : ∀ a : L.ι, e ⁻¹ᵁ L.U a ≤ V.ι ''ᵁ (L.pull (V.ι ≫ e)).U (fun _ => a) := by
    intro a y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y hy
    exact V.ι.apply_mem_image_iff.2 (mem_pull.2 hy)
  refine ⟨fun a => res (hle a) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => a)), ?_⟩
  intro y a b ha hb
  obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y ha
  have key : ∀ c : L.ι, e (V.ι v) ∈ L.U c →
      gm V.ι v (e ⁻¹ᵁ L.U c) (res (hle c) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => c))) =
        gm (𝟙 V.toScheme) v _ (t.s fun _ => c) := by
    intro c hc
    have hm : (𝟙 V.toScheme) v ∈ (L.pull (V.ι ≫ e)).U (fun _ => c) := mem_pull.2 hc
    rw [gm_res V.ι v (hle c) (show V.ι v ∈ e ⁻¹ᵁ L.U c from hc)]
    have := GlobalTheory.GlueLineBundle.gm_imU V.ι (𝟙 V.toScheme) v _ hm (t.s fun _ => c)
    rwa [Category.id_comp] at this
  have hinj : Function.Injective (Units.map (V.ι.stalkMap v).hom.toMonoidHom) :=
    Units.map_injective (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_mul, stalkMap_gm, stalkMap_gm, stalkMap_gm, Category.comp_id]
  beta_reduce
  rw [key a ha, key b hb,
    (isGen_iff_germ t).1 ht v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    gm_pull_g L (V.ι ≫ e) (𝟙 V.toScheme) v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    Category.id_comp]

end GlobalTheory.PicGlue
