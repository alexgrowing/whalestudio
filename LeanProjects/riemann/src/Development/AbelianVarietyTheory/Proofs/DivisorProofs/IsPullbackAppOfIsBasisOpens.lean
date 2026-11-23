import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchBasis

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

lemma app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {W V : Y.Opens} (i : W ⟶ V) (s : Γ(Y, V)) :
    (f.app W).hom ((Y.presheaf.map i.op).hom s) =
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op).hom ((f.app V).hom s) :=
  congrArg (fun φ => φ.hom s) (f.naturality i.op)

lemma appLE_res {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) (e : V ≤ g ⁻¹ᵁ U) (e' : V' ≤ g ⁻¹ᵁ U') (b : Γ(Y, U)) :
    (g.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom b) =
      (X.presheaf.map (homOfLE hV).op).hom ((g.appLE U V e).hom b) := by
  have h1 := congrArg (fun φ => φ.hom b) (g.map_appLE e' (homOfLE hU).op)
  have h2 := congrArg (fun φ => φ.hom b) (g.appLE_map e (homOfLE hV).op)
  exact h1.trans h2.symm

lemma res_res (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (s : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  have := congrArg (fun φ => φ.hom s) (X.presheaf.map_comp i.op j.op)
  exact this.symm.trans rfl

theorem isPullback_app_of_isBasis : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 h𝒱 hP
  have hle : ∀ V : Y.Opens, (i₁ ≫ j₁) ⁻¹ᵁ V ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ V) := fun V => by rw [hw]; exact le_rfl
  have hcomm : ∀ V : Y.Opens, j₁.app V ≫ i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl =
      j₂.app V ≫ i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V) := by
    intro V
    have key : ∀ (k k' : Y₀ ⟶ Y), k = k' → ∀ (e : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k ⁻¹ᵁ V)
        (e' : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k' ⁻¹ᵁ V), k.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e = k'.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e' := by
      rintro k _ rfl e e'; rfl
    exact (Scheme.Hom.comp_appLE i₁ j₁ V _ le_rfl).symm.trans
      ((key _ _ hw _ _).trans (Scheme.Hom.comp_appLE i₂ j₂ V _ (hle V)))
  have hcovY : ∀ U : Y.Opens, U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, W.1 := by
    intro U y hy
    obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hyW⟩
  have hcov : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens),
      f ⁻¹ᵁ U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, f ⁻¹ᵁ W.1 := by
    intro Z f U z hz
    obtain ⟨W, hW, hzW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 (x := f z) hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hzW⟩

  have inj : ∀ (U : Y.Opens) (s t : Γ(Y, U)), (j₁.app U).hom s = (j₁.app U).hom t →
      (j₂.app U).hom s = (j₂.app U).hom t → s = t := by
    intro U s t h₁ h₂
    refine Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U} => W.1) U
      (fun W => homOfLE W.2.2) (hcovY U) s t ?_
    rintro ⟨W, hW, hWU⟩
    obtain ⟨hinj, -⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
    apply hinj
    · exact (app_res j₁ (homOfLE hWU) s).trans ((congrArg _ h₁).trans (app_res j₁ (homOfLE hWU) t).symm)
    · exact (app_res j₂ (homOfLE hWU) s).trans ((congrArg _ h₂).trans (app_res j₂ (homOfLE hWU) t).symm)

  have surj : ∀ (V : Y.Opens) (b : Γ(Y₁, j₁ ⁻¹ᵁ V)) (c : Γ(Y₂, j₂ ⁻¹ᵁ V)),
      (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl).hom b =
        (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V)).hom c →
      ∃ a, (j₁.app V).hom a = b ∧ (j₂.app V).hom a = c := by
    intro V b c hbc
    have loc : ∀ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V}, ∃ a : Γ(Y, W.1),
        (j₁.app W.1).hom a = (Y₁.presheaf.map (homOfLE (j₁.preimage_mono W.2.2)).op).hom b ∧
        (j₂.app W.1).hom a = (Y₂.presheaf.map (homOfLE (j₂.preimage_mono W.2.2)).op).hom c := by
      rintro ⟨W, hW, hWV⟩
      obtain ⟨-, hex⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
      apply hex
      have e1 := appLE_res i₁ (j₁.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) le_rfl le_rfl b
      have e2 := appLE_res i₂ (j₂.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) (hle V) (hle W) c
      exact e1.trans ((congrArg _ hbc).trans e2.symm)
    choose sf hsf₁ hsf₂ using loc
    have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) sf := by
      intro W W'
      apply inj
      · refine (app_res j₁ _ _).trans (Eq.trans ?_ (app_res j₁ _ _).symm)
        rw [hsf₁, hsf₁]
        exact (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).trans
          (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).symm
      · refine (app_res j₂ _ _).trans (Eq.trans ?_ (app_res j₂ _ _).symm)
        rw [hsf₂, hsf₂]
        exact (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).trans
          (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).symm
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) V
      (fun W => homOfLE W.2.2) (hcovY V) sf hcompat
    refine ⟨s, ?_, ?_⟩
    · refine Y₁.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₁ ⁻¹ᵁ W.1) (j₁ ⁻¹ᵁ V)
        (fun W => homOfLE (j₁.preimage_mono W.2.2)) (hcov j₁ V) _ _ ?_
      intro W
      exact (app_res j₁ (homOfLE W.2.2) s).symm.trans ((congrArg (j₁.app W.1).hom (hs W)).trans (hsf₁ W))
    · refine Y₂.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₂ ⁻¹ᵁ W.1) (j₂ ⁻¹ᵁ V)
        (fun W => homOfLE (j₂.preimage_mono W.2.2)) (hcov j₂ V) _ _ ?_
      intro W
      exact (app_res j₂ (homOfLE W.2.2) s).symm.trans ((congrArg (j₂.app W.1).hom (hs W)).trans (hsf₂ W))
  intro V
  exact (isPullback_iff_elem _ _ _ _ (hcomm V)).2 ⟨fun x y hx hy => inj V x y hx hy, surj V⟩

end GlobalTheory.PinchBasis
