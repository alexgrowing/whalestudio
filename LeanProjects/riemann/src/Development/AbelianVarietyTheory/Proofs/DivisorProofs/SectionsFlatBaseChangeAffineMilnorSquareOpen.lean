import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommRingCatIsPullbackFlatBaseChangeSurjectiveStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem isPushout_app_of_isPullback {X X₁ T T₁ : Scheme.{0}} {f : X₁ ⟶ X} {p₁ : X₁ ⟶ T₁} {p : X ⟶ T}
    {j : T₁ ⟶ T} (h : IsPullback f p₁ p j) [IsAffine T] [IsAffine T₁] {W : X.Opens}
    (hW : IsAffineOpen W) :
    IsAffineOpen (f ⁻¹ᵁ W) ∧
      IsPushout (p.appLE ⊤ W le_top) j.appTop (f.app W) (p₁.appLE ⊤ (f ⁻¹ᵁ W) le_top) := by
  have : IsAffine W.toScheme := hW
  have sq : IsPullback (f ∣_ W) ((f ⁻¹ᵁ W).ι ≫ p₁) (W.ι ≫ p) j :=
    (isPullback_morphismRestrict f W).paste_vert h
  have : IsAffine (f ⁻¹ᵁ W).toScheme := IsAffine.of_isPullback sq
  refine ⟨this, ?_⟩
  exact (ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip inferInstance (isAffineOpen_top T) hW le_top le_top).flip

theorem appLE_congr_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ a ⁻¹ᵁ U) (h' : V ≤ b ⁻¹ᵁ U) : a.appLE U V h = b.appLE U V h' := by
  subst e; rfl

theorem isPullback_app_of_affine {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W))
    (hV : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V) :
    IsPullback (f₁.app W) (f₂.app W) (g₁.appLE _ V hV₁) (g₂.appLE _ V hV₂) := by
  have := hM.aff; have := hM.aff₁; have := hM.aff₂; have := hM.closed
  obtain ⟨hT₀, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine k₂
  obtain ⟨hU₁, P₁⟩ := isPushout_app_of_isPullback h₁ hW
  obtain ⟨hU₂, P₂⟩ := isPushout_app_of_isPullback h₂ hW
  obtain ⟨-, P₀⟩ := isPushout_app_of_isPullback h₀ hU₂
  have hVe : V = g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := by
    refine le_antisymm hV₂ ?_
    have : g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
    exact this.le.trans hV
  subst hVe
  have e₂ : g₂.appLE (f₂ ⁻¹ᵁ W) (g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) hV₂ = g₂.app (f₂ ⁻¹ᵁ W) :=
    Scheme.Hom.appLE_eq_app ..
  rw [e₂]
  have hfl : (p.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  refine GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective _ _ _ _ _ _ _ _ j₁.appTop j₂.appTop k₁.appTop k₂.appTop hM.cart hsurj _ _ _ _ _ _ _ _
    hfl P₁ P₂ P₀ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_eq hg _ _ _ _
  · have : k₁.appTop = k₁.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app ..).symm
    rw [this]
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    exact appLE_congr_eq hp _ _ _ _

theorem app_restrict_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U W : Y.Opens} (h : U ≤ W) (a : Γ(Y, W)) :
    f.app U (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem appLE_restrict_eq {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (h : V ≤ g ⁻¹ᵁ U) (h' : V' ≤ g ⁻¹ᵁ U') (a : Γ(Y, U)) :
    g.appLE U' V' h' (Y.presheaf.map (homOfLE hU).op a) =
      X.presheaf.map (homOfLE hV).op (g.appLE U V h a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem elem_of_isPullback_ring {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {i : C ⟶ D} (H : IsPullback f g h i) :
    (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ b c, h b = i c → ∃ a, f a = b ∧ g a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem sections_of_squares {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] (W : X.Opens) :
    (∀ a b : Γ(X, W), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b) ∧
    ∀ (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)),
      g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)),
        g₁.appLE _ V hV₁ a₁ = g₂.appLE _ V hV₂ a₂ →
          ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂ := by
  have hpre : ∀ U : X.Opens, g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ U) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) := fun U ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
  have aff : ∀ U : X.Opens, IsAffineOpen U → IsPullback (f₁.app U) (f₂.app U)
      (g₁.appLE _ (g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U)) le_rfl) (g₂.appLE _ _ (hpre U).ge) :=
    fun U hU ↦ isPullback_app_of_affine hM h₁ h₂ h₀ hg hp hU _ le_rfl (hpre U).ge le_rfl
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), f₁.app U a = f₁.app U b →
      f₂.app U a = f₂.app U b → a = b := by
    intro U a b ha hb
    refine TopCat.Presheaf.section_ext X.sheaf U a b fun x hx ↦ ?_
    change X.presheaf.germ U x hx a = X.presheaf.germ U x hx b
    obtain ⟨U', hU', hxU', hle⟩ := exists_isAffineOpen_mem_and_subset hx
    have hle' : U' ≤ U := hle
    rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxU' a,
      ← X.presheaf.germ_res_apply (homOfLE hle') x hxU' b]
    congr 1
    refine (elem_of_isPullback_ring (aff U' hU')).1 _ _ ?_ ?_
    · rw [app_restrict_eq, app_restrict_eq, ha]
    · rw [app_restrict_eq, app_restrict_eq, hb]
  refine ⟨inj W, ?_⟩
  intro V hV₁ hV₂ hV a₁ a₂ he
  have loc : ∀ x : W, ∃ U : X.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧ ∃ hUW : U ≤ W, ∃ c : Γ(X, U),
      f₁.app U c = X₁.presheaf.map (homOfLE (f₁.preimage_mono hUW)).op a₁ ∧
      f₂.app U c = X₂.presheaf.map (homOfLE (f₂.preimage_mono hUW)).op a₂ := by
    intro x
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset x.2
    have hUW : U ≤ W := hle
    refine ⟨U, hU, hxU, hUW, (elem_of_isPullback_ring (aff U hU)).2 _ _ ?_⟩
    have hVU : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) ≤ V := (g₁.preimage_mono (f₁.preimage_mono hUW)).trans hV
    rw [appLE_restrict_eq g₁ (f₁.preimage_mono hUW) hVU hV₁,
      appLE_restrict_eq g₂ (f₂.preimage_mono hUW) hVU hV₂, he]
  choose U hU hxU hUW c hc₁ hc₂ using loc
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro x y
    change X.presheaf.map (homOfLE (inf_le_left : U x ⊓ U y ≤ U x)).op (c x) =
      X.presheaf.map (homOfLE (inf_le_right : U x ⊓ U y ≤ U y)).op (c y)
    apply inj
    · rw [app_restrict_eq, app_restrict_eq, hc₁, hc₁, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [app_restrict_eq, app_restrict_eq, hc₂, hc₂, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' U W (fun x ↦ homOfLE (hUW x))
    (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩) c compat
  have ha' : ∀ x, X.presheaf.map (homOfLE (hUW x)).op a = c x := ha
  refine ⟨a, ?_, ?_⟩
  · refine TopCat.Presheaf.section_ext X₁.sheaf _ _ _ fun y hy ↦ ?_
    change X₁.presheaf.germ _ y hy _ = X₁.presheaf.germ _ y hy _
    have hyU : y ∈ f₁ ⁻¹ᵁ U ⟨f₁ y, hy⟩ := hxU ⟨f₁ y, hy⟩
    rw [← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU,
      ← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU a₁,
      ← app_restrict_eq f₁ (hUW ⟨f₁ y, hy⟩) a, ha' ⟨f₁ y, hy⟩, hc₁]
  · refine TopCat.Presheaf.section_ext X₂.sheaf _ _ _ fun y hy ↦ ?_
    change X₂.presheaf.germ _ y hy _ = X₂.presheaf.germ _ y hy _
    have hyU : y ∈ f₂ ⁻¹ᵁ U ⟨f₂ y, hy⟩ := hxU ⟨f₂ y, hy⟩
    rw [← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU,
      ← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU a₂,
      ← app_restrict_eq f₂ (hUW ⟨f₂ y, hy⟩) a, ha' ⟨f₂ y, hy⟩, hc₂]

theorem sections_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ W : (A ⊗ T).left.Opens, (∀ a b : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = (A ◁ j₁).left.app W b → (A ◁ j₂).left.app W a = (A ◁ j₂).left.app W b → a = b) ∧ ∀ (V : (A ⊗ T₀).left.Opens) (h₁ : V ≤ (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W)) (h₂ : V ≤ (A ◁ k₂).left ⁻¹ᵁ ((A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ((A ⊗ T₁).left, (A ◁ j₁).left ⁻¹ᵁ W)) (a₂ : Γ((A ⊗ T₂).left, (A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left.appLE _ V h₁ a₁ = (A ◁ k₂).left.appLE _ V h₂ a₂ → ∃ a : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = a₁ ∧ (A ◁ j₂).left.app W a = a₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM W
  have : Flat (snd A T).left := inferInstanceAs (Flat (pullback.snd A.hom T.hom))
  have hw : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have hg : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hw]
  have hp : (A ◁ k₁).left ≫ (snd A T₁).left = (snd A T₀).left ≫ k₁.left := by
    rw [← Over.comp_left, ← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd]
  exact sections_of_squares hM (isPullback_whiskerLeft_snd_left A j₁)
    (isPullback_whiskerLeft_snd_left A j₂) (isPullback_whiskerLeft_snd_left A k₂) hg hp W

end GlobalTheory.DualOpen
