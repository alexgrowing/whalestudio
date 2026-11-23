import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_map_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val _ (f y) U h, ← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem isoOn_of_lbIso (X : Scheme.{0}) (W : X.Opens) (L M : LB X) (h : LBIso (L.pull W.ι) (M.pull W.ι)) :
    ∃ w : Cmp W L M, IsoOn W L M w := by
  obtain ⟨s, hs⟩ := h
  have hle : ∀ (a : L.ι) (b : M.ι), W ⊓ (L.U a ⊓ M.U b) ≤
      W.ι ''ᵁ ((M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a)) := by
    intro a b x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx.1⟩, rfl⟩
    exact W.ι.apply_mem_image_iff.2 ⟨mem_pull.2 hx.2.2, mem_pull.2 hx.2.1⟩
  refine ⟨fun a b => (res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹, ?_⟩
  intro x hx a a' b b' ha ha' hb hb'
  obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have E : ∀ (a : L.ι) (b : M.ι), W.ι y ∈ L.U a → W.ι y ∈ M.U b →
      gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) =
      (gm (𝟙 _) y _ (s.s (fun _ => b, fun _ => a)))⁻¹ := by
    intro a b ha hb
    have hm : W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) := ⟨hx, ha, hb⟩
    have hv : (𝟙 W.toScheme) y ∈ (M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a) :=
      ⟨mem_pull.2 hb, mem_pull.2 ha⟩
    have e := GlobalTheory.GlueLineBundle.gm_imU W.ι (𝟙 _) y _ hv (s.s (fun _ => b, fun _ => a))
    rw [Category.id_comp] at e
    rw [map_inv, gm_res W.ι y (hle a b) hm, e]
    rfl
  have EL : ∀ (a a' : L.ι), W.ι y ∈ L.U a → W.ι y ∈ L.U a' →
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') = gm (𝟙 _) y _ ((L.pull W.ι).g (fun _ => a) (fun _ => a')) := by
    intro a a' ha ha'
    have e := gm_pull_g L W.ι (𝟙 _) y (fun _ => a) (fun _ => a') (mem_pull.2 ha) (mem_pull.2 ha')
    rw [Category.id_comp] at e
    exact e.symm
  have EM : ∀ (b b' : M.ι), W.ι y ∈ M.U b → W.ι y ∈ M.U b' →
      gm W.ι y (M.U b ⊓ M.U b') (M.g b b') = gm (𝟙 _) y _ ((M.pull W.ι).g (fun _ => b) (fun _ => b')) := by
    intro b b' hb hb'
    have e := gm_pull_g M W.ι (𝟙 _) y (fun _ => b) (fun _ => b') (mem_pull.2 hb) (mem_pull.2 hb')
    rw [Category.id_comp] at e
    exact e.symm
  have hp : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b, fun _ => a) := ⟨mem_pull.2 hb, mem_pull.2 ha⟩
  have hq : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b', fun _ => a') := ⟨mem_pull.2 hb', mem_pull.2 ha'⟩
  have G := (isGen_iff_germ s).1 hs y _ _ hp hq
  rw [gm_div' (M.pull W.ι) (L.pull W.ι) (𝟙 _) y _ _ hp hq] at G
  have alg : ∀ {Gp : Type} [CommGroup Gp] (S Mg large₂ S' : Gp), S = Mg * large₂⁻¹ * S' → S⁻¹ * Mg = large₂ * S'⁻¹ := by
    intro Gp _ S Mg large₂ S' e
    rw [e, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    exact _root_.mul_comm _ _
  have key : gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) *
        gm W.ι y (M.U b ⊓ M.U b') (M.g b b') =
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') * gm W.ι y (W ⊓ (L.U a' ⊓ M.U b'))
        ((res (hle a' b') (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b', fun _ => a'))))⁻¹) := by
    rw [E a b ha hb, E a' b' ha' hb', EL a a' ha ha', EM b b' hb hb']
    exact alg _ _ _ _ G
  have hinj : Function.Injective (Units.map (W.ι.stalkMap y).hom.toMonoidHom) := fun u v e =>
    Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1 (congrArg Units.val e))
  apply hinj
  rw [map_mul, map_mul, ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) from ⟨hx, ha, hb⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ M.U b ⊓ M.U b' from ⟨hb, hb'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ L.U a ⊓ L.U a' from ⟨ha, ha'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a' ⊓ M.U b') from ⟨hx, ha', hb'⟩)]
  exact key

end GlobalTheory.PicGlue
