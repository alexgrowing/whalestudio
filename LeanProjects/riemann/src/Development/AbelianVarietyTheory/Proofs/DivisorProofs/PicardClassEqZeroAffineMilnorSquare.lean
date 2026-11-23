import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    (h : CechPic.pull f (cls L hL) = 0) : ∃ b : ∀ i, Γ(Y, f ⁻¹ᵁ L.U i)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), f (r z) ∈ L.U i → f (r z) ∈ L.U j →
        gm r z _ (b i) = gm (r ≫ f) z _ (L.g i j) * gm r z _ (b j) := by
  rw [← cls_pull hL f (pull_isLB hL f)] at h
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 h
  have le : ∀ i, f ⁻¹ᵁ L.U i ≤ (L.pull f).U (fun _ ↦ i) := fun i y hy ↦ mem_pull.2 hy
  refine ⟨fun i ↦ res (le i) (t.s fun _ ↦ i), fun Z r z i j hi hj ↦ ?_⟩
  have mi : r z ∈ (L.pull f).U (fun _ ↦ i) := mem_pull.2 hi
  have mj : r z ∈ (L.pull f).U (fun _ ↦ j) := mem_pull.2 hj
  have hm : r z ∈ (L.pull f).U (fun _ ↦ i) ⊓ (L.pull f).U (fun _ ↦ j) := ⟨mi, mj⟩
  have e := congrArg (gm r z _) (ht (fun _ ↦ i) (fun _ ↦ j))
  rw [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull_g L f r z _ _ mi mj] at e
  rw [gm_res r z (le i) hi, gm_res r z (le j) hj]
  exact e

theorem eq_zero_of_square {X X₁ X₂ X₀ : Scheme.{0}} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (g₁ : X₀ ⟶ X₁) (g₂ : X₀ ⟶ X₂)
    (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b)
    (ex : ∀ (W : X.Opens) (h₂ : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W))
      (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)), g₁.appLE _ _ le_rfl a₁ = g₂.appLE _ _ h₂ a₂ →
        ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂)
    (lift : Function.Surjective (Units.map g₂.appTop.hom.toMonoidHom))
    (c : Pic X) (h₁ : CechPic.pull f₁ c = 0) (h₂ : CechPic.pull f₂ c = 0) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨b₁, hb₁⟩ := exists_units_of_pull_eq_zero hL f₁ h₁
  obtain ⟨b₂, hb₂⟩ := exists_units_of_pull_eq_zero hL f₂ h₂
  have le : ∀ W : X.Opens, g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := fun W ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have injU : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU f₁ W a = pullU f₁ W b → pullU f₂ W a = pullU f₂ W b → a = b :=
    fun W a b e₁ e₂ ↦ Units.ext (inj W _ _ (congrArg Units.val e₁) (congrArg Units.val e₂))
  have exU : ∀ (W : X.Opens) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)ˣ) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)ˣ),
      res le_rfl (pullU g₁ _ a₁) = res (le W) (pullU g₂ _ a₂) →
        ∃ a : Γ(X, W)ˣ, pullU f₁ W a = a₁ ∧ pullU f₂ W a = a₂ := fun W a₁ a₂ e ↦ by
    have e' : res le_rfl (pullU g₁ _ a₁⁻¹) = res (le W) (pullU g₂ _ a₂⁻¹) := by
      rw [map_inv, map_inv, map_inv, map_inv, e]
    obtain ⟨a, p₁, p₂⟩ := ex W (le W) a₁.val a₂.val (congrArg Units.val e)
    obtain ⟨a', q₁, q₂⟩ := ex W (le W) (a₁⁻¹).val (a₂⁻¹).val (congrArg Units.val e')
    have k : a * a' = 1 := inj W _ _ (by rw [map_mul, map_one, p₁, q₁, Units.mul_inv])
      (by rw [map_mul, map_one, p₂, q₂, Units.mul_inv])
    exact ⟨⟨a, a', k, (mul_comm _ _).trans k⟩, Units.ext p₁, Units.ext p₂⟩
  have key : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y ↦ by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  let V : L.ι → X₀.Opens := fun i ↦ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ L.U i)
  let q : ∀ i, Γ(X₀, V i)ˣ := fun i ↦ pullU g₁ _ (b₁ i) * (res (le _) (pullU g₂ _ (b₂ i)))⁻¹
  have gq : ∀ i x, x ∈ V i → gm (𝟙 X₀) x (V i) (q i) = gm g₁ x _ (b₁ i) * (gm g₂ x _ (b₂ i))⁻¹ := fun i x hx ↦ by
    have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
    have e₂ := (gm_res (𝟙 X₀) x (le (L.U i)) hx _).trans (gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i))
    rw [Category.id_comp] at e₁ e₂
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg (·⁻¹) e₂)))
  obtain ⟨F, hF⟩ := glue_unit ⊤ V (fun _ ↦ le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := exists_chart hL (f₁ (g₁ x))
      exact Opens.mem_iSup.2 ⟨i, hi⟩) q (fun i j x hx ↦ by
      rw [gq i x hx.1, gq j x hx.2, hb₁ _ g₁ x i j hx.1 hx.2, hb₂ _ g₂ x i j (le _ hx.1) (le _ hx.2), w, key])
  obtain ⟨u, hu⟩ := lift F
  have hu' : pullU g₂ ⊤ u = F := hu
  have loc : ∀ i, ∃ s : Γ(X, L.U i)ˣ, pullU f₁ _ s = b₁ i ∧ pullU f₂ _ s = b₂ i * res le_top u := fun i ↦
    exU _ _ _ (unit_ext fun x hx ↦ by
      have e := congrArg (gm (𝟙 X₀) x (V i)) (hF i)
      rw [gm_res (𝟙 X₀) x _ hx, gq i x hx, ← hu'] at e
      have e₀ := gm_pull (𝟙 X₀) g₂ x ⊤ trivial u
      have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
      have e₂ := gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i * res le_top u)
      rw [Category.id_comp] at e₀ e₁ e₂
      rw [gm_res (𝟙 X₀) x _ hx, gm_res (𝟙 X₀) x _ hx, e₁, e₂, map_mul, gm_res g₂ x _ (le _ hx), ← e₀]
      exact (mul_inv_eq_iff_eq_mul.1 e.symm).trans (mul_comm _ _))
  choose s hs₁ hs₂ using loc
  have gp : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (W : X.Opens) (a : Γ(X, W)ˣ), f y ∈ W →
      gm (𝟙 Y) y (f ⁻¹ᵁ W) (pullU f W a) = gm f y W a := fun f y W a hy ↦
    (gm_pull (𝟙 _) f y W hy a).trans (by rw [Category.id_comp])
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, fun i j ↦ injU _ _ _ (unit_ext fun y hy ↦ ?_) (unit_ext fun y hy ↦ ?_)⟩
  · have e := hb₁ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp, ← hs₁, ← hs₁, gp f₁ y _ _ hy.1, gp f₁ y _ _ hy.2] at e
    rw [gp f₁ y _ _ hy, gp f₁ y _ _ hy, map_mul, gm_res f₁ y _ hy, gm_res f₁ y _ hy]
    exact e
  · have e := hb₂ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp] at e
    have k : ∀ i, f₂ y ∈ L.U i → gm f₂ y _ (s i) = gm (𝟙 _) y _ (b₂ i) * gm (𝟙 _) y ⊤ u := fun i hi ↦ by
      rw [← gp f₂ y _ _ hi, hs₂, map_mul, gm_res (𝟙 _) y _ hi]
    rw [gp f₂ y _ _ hy, gp f₂ y _ _ hy, map_mul, gm_res f₂ y _ hy, gm_res f₂ y _ hy]
    exact (k i hy.1).trans (by rw [e, k j hy.2, _root_.mul_assoc])

theorem pic_eq_zero_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left →
    Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ h hs
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ h
  have w : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext h.w
  refine eq_zero_of_square _ _ (A ◁ k₁).left (A ◁ k₂).left ?_ (fun W ↦ (H W).1)
    (fun W h₂ ↦ (H W).2 _ le_rfl h₂ le_rfl) hs
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w]

end GlobalTheory.DualOpen
