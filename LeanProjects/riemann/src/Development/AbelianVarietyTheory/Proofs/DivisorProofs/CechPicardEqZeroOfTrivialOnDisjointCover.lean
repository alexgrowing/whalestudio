import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PicDisj

open TopologicalSpace

theorem map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) = gm f y U a := by
  refine Units.ext ?_
  rw [gm, gm, dif_pos h, dif_pos (show (𝟙 X : X ⟶ X) (f y) ∈ U from h)]
  exact Scheme.Hom.germ_stalkMap_apply f U y h a.val

theorem gm_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) (V : Y.Opens) (h : y ∈ V) (a : Γ(Y, V)ˣ) :
    gm f y (f ''ᵁ V) (Units.map (f.appIso V).inv.hom.toMonoidHom a) = gm (𝟙 Y) y V a := by
  refine Units.ext ?_
  have h' : f y ∈ f ''ᵁ V := ⟨y, h, rfl⟩
  rw [gm, gm, dif_pos h', dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ V from h)]
  change (Y.presheaf.germ (f ⁻¹ᵁ (f ''ᵁ V)) y h').hom (((f.appIso V).inv ≫ f.app (f ''ᵁ V)).hom a.val) =
    (Y.presheaf.germ V y h).hom a.val
  rw [Scheme.Hom.appIso_inv_app]
  exact Y.presheaf.germ_res_apply _ y _ _

theorem exists_gen_of_rel {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) (P : N.ι → ∀ y : Y, (Y.presheaf.stalk y)ˣ → Prop)
    (loc : ∀ p, ∀ y ∈ N.U p, ∃ W : Y.Opens, W ≤ N.U p ∧ y ∈ W ∧ ∃ s : Γ(Y, W)ˣ, ∀ y' ∈ W, P p y' (gm (𝟙 Y) y' W s))
    (cmp : ∀ p q y u u', y ∈ N.U p → y ∈ N.U q → P p y u → P q y u' → u = gm (𝟙 Y) y _ (N.g p q) * u') :
    ∃ t : N.Gen, t.IsGen := by
  have uniq : ∀ p y u u', y ∈ N.U p → P p y u → P p y u' → u = u' := fun p y u u' hy h h' => by
    have e := gm_cocycle hN (𝟙 Y) y hy hy hy
    rw [cmp p p y u u' hy hy h h', mul_eq_left.1 e, _root_.one_mul]
  have key : ∀ p, ∃ a : Γ(Y, N.U p)ˣ, ∀ y ∈ N.U p, P p y (gm (𝟙 Y) y _ a) := fun p => by
    choose W hW hy s hs using fun y : (N.U p : Set Y) => loc p y.1 y.2
    have cp : ∀ k l, res (inf_le_left : W k ⊓ W l ≤ W k) (s k) = res inf_le_right (s l) := fun k l =>
      unit_ext fun y h => by
        rw [gm_res _ y _ h, gm_res _ y _ h]
        exact uniq p y _ _ (hW k h.1) (hs k y h.1) (hs l y h.2)
    have hc : N.U p ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy _⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (N.U p) (fun k => homOfLE (hW k)) hc (fun k => (s k).val)
      fun k l => congrArg Units.val (cp k l)
    have hu : IsUnit (M := Γ(Y, N.U p)) b := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
      have := (s ⟨x, hx⟩).isUnit.map (Y.presheaf.germ _ x (hy ⟨x, hx⟩)).hom
      rw [← hb] at this
      exact (Y.presheaf.germ_res_apply (homOfLE (hW ⟨x, hx⟩)) x (hy ⟨x, hx⟩) b) ▸ this
    refine ⟨hu.unit, fun y h => ?_⟩
    have e : res (hW ⟨y, h⟩) hu.unit = s ⟨y, h⟩ := Units.ext (hb _)
    rw [← gm_res _ y (hW ⟨y, h⟩) (hy ⟨y, h⟩), e]
    exact hs _ y (hy _)
  choose a ha using key
  exact ⟨⟨a⟩, (isGen_iff_germ _).2 fun y i j hi hj => cmp i j y _ _ hi hj (ha i y hi) (ha j y hj)⟩

theorem eq_zero_of_pull_eq_zero : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  intro Y κ _ Z f _ hcov hdis d hd
  obtain ⟨L, hL, rfl⟩ := cls_surj d
  choose t ht using fun i => (cls_eq_zero_iff (pull_isLB hL (f i))).1 (hd i)
  have surj : ∀ y : Y, ∃ i z, f i z = y := fun y => by
    have : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.1 this
    exact ⟨i, z, hz⟩
  refine (cls_eq_zero_iff hL).2 (exists_gen_of_rel hL (fun p y u => ∀ i (z : Z i) (u' : (Y.presheaf.stalk (f i z))ˣ),
    f i z = y → HEq u' u → Units.map ((f i).stalkMap z).hom.toMonoidHom u' =
      gm (𝟙 _) z ((L.pull (f i)).U fun _ => p) ((t i).s fun _ => p)) ?_ ?_)
  · intro p y hy
    obtain ⟨i, z, rfl⟩ := surj y
    refine ⟨f i ''ᵁ ((L.pull (f i)).U fun _ => p), ?_, ⟨z, mem_pull.2 hy, rfl⟩,
      Units.map ((f i).appIso _).inv.hom.toMonoidHom ((t i).s fun _ => p), ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_pull.1 hw
    · rintro y' ⟨w, hw, hy'⟩ j z' u' rfl hu
      obtain rfl : i = j := by
        by_contra hne
        have hm : f j z' ∈ (f i).opensRange ⊓ (f j).opensRange := ⟨⟨w, hy'⟩, ⟨z', rfl⟩⟩
        rw [(hdis hne).eq_bot] at hm
        exact hm
      obtain rfl : w = z' := (f i).isOpenEmbedding.injective hy'
      rw [eq_of_heq hu, map_gm (f i) w _ (show f i w ∈ f i ''ᵁ ((L.pull (f i)).U fun _ => p) from ⟨w, hw, rfl⟩), gm_image _ _ _ hw]
  · intro p q y u u' hp hq h h'
    obtain ⟨i, z, rfl⟩ := surj y
    apply Units.map_injective (f := ((f i).stalkMap z).hom.toMonoidHom)
      (ConcreteCategory.bijective_of_isIso ((f i).stalkMap z)).1
    rw [map_mul, h i z u rfl HEq.rfl, h' i z u' rfl HEq.rfl, map_gm (f i) z (L.U p ⊓ L.U q) ⟨hp, hq⟩,
      (isGen_iff_germ _).1 (ht i) z (fun _ => p) (fun _ => q) (mem_pull.2 hp) (mem_pull.2 hq),
      gm_pull_g L (f i) (𝟙 _) z _ _ (mem_pull.2 hp) (mem_pull.2 hq), Category.id_comp]

end GlobalTheory.PicDisj
