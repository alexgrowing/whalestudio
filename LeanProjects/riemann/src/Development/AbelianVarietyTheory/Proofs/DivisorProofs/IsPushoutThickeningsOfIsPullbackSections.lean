import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ThickPush

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem isUnit_germ_of_eq {T : Scheme.{0}} {p q : T} (hpq : p = q) (W : T.Opens) (hp : p ∈ W) (hq : q ∈ W)
    (t : Γ(T, W)) (h : IsUnit (T.presheaf.germ W p hp t)) : IsUnit (T.presheaf.germ W q hq t) := by
  subst hpq; exact h

section Desc
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def bse : (Y : TopCat) ⟶ (T : TopCat) :=
  TopCat.ofHom ⟨fun y => g₁ ((hj.homeomorph _).symm y),
    g₁.base.hom.continuous.comp (hj.homeomorph _).symm.continuous⟩

theorem bse_j₁ (x : Y₁) : bse hj g₁ (j₁ x) = g₁ x := by
  show g₁ ((hj.homeomorph _).symm (hj.homeomorph _ x)) = g₁ x
  rw [Homeomorph.symm_apply_apply]

include hw hi₂ hg in
theorem bse_j₂ (x : Y₂) : bse hj g₁ (j₂ x) = g₂ x := by
  obtain ⟨y, rfl⟩ := hi₂ x
  have h1 : j₂ (i₂ y) = j₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  have h2 : g₂ (i₂ y) = g₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  rw [h1, h2, bse_j₁]

theorem pre₁ (W : T.Opens) : j₁ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₁ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₁ x) ∈ W ↔ g₁ x ∈ W
  rw [bse_j₁]

include hw hi₂ hg in
theorem pre₂ (W : T.Opens) : j₂ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₂ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₂ x) ∈ W ↔ g₂ x ∈ W
  rw [bse_j₂ hw hi₂ hj g₁ g₂ hg]

end Desc

section Lift
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def liftApp (W : T.Opens) : Γ(T, W) ⟶ Γ(Y, (TopologicalSpace.Opens.map (bse hj g₁)).obj W) :=
  (hV _).lift (g₁.appLE W _ (pre₁ hj g₁ W).le) (g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le) (by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq hg _ _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm))

@[reassoc]
theorem liftApp_fst (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₁.app _ = g₁.appLE W _ (pre₁ hj g₁ W).le :=
  (hV _).lift_fst _ _ _

@[reassoc]
theorem liftApp_snd (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₂.app _ =
    g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le :=
  (hV _).lift_snd _ _ _

def psh : Y.toPresheafedSpace ⟶ T.toPresheafedSpace where
  base := bse hj g₁
  c :=
    { app := fun W => liftApp hw hi₂ hj hV g₁ g₂ hg W.unop
      naturality := fun W W' i => by
        apply (hV _).hom_ext
        · simp only [Category.assoc]
          erw [liftApp_fst, Scheme.Hom.naturality, liftApp_fst_assoc]
          simp
        · simp only [Category.assoc]
          erw [liftApp_snd, Scheme.Hom.naturality, liftApp_snd_assoc]
          simp }

end Lift

section Hom
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def desc : Y ⟶ T :=
  ⟨⟨psh hw hi₂ hj hV g₁ g₂ hg, fun x => ⟨fun a ha => by
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    obtain ⟨W, hW, t, rfl⟩ := T.presheaf.germ_exist (x := (psh hw hi₂ hj hV g₁ g₂ hg).base (j₁ x₁)) a
    have h1 := PresheafedSpace.stalkMap_germ_apply (psh hw hi₂ hj hV g₁ g₂ hg) W (j₁ x₁) hW t
    erw [h1] at ha
    have h2 : IsUnit ((Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t))) := by
      erw [← Scheme.Hom.germ_stalkMap_apply]; exact ha.map (j₁.stalkMap x₁).hom
    have h3 : (j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t) =
        (g₁.appLE W _ (pre₁ hj g₁ W).le).hom t := by
      rw [← CommRingCat.comp_apply, liftApp_fst]
    erw [h3] at h2
    have hx₁ : g₁ x₁ ∈ W := by rw [← bse_j₁ hj g₁ x₁]; exact hW
    have h4 : (Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((g₁.appLE W _ (pre₁ hj g₁ W).le).hom t) = g₁.stalkMap x₁ (T.presheaf.germ W (g₁ x₁) hx₁ t) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
    rw [h4] at h2
    exact isUnit_germ_of_eq (bse_j₁ hj g₁ x₁).symm W hx₁ hW t (isUnit_of_map_unit (g₁.stalkMap x₁).hom _ h2)⟩⟩⟩

theorem desc_app (W : T.Opens) : (desc hw hi₂ hj hV g₁ g₂ hg).app W = liftApp hw hi₂ hj hV g₁ g₂ hg W := rfl

end Hom

section Fac
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

theorem fac₁ : j₁ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₁ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₁ hj g₁ x
  · have hh : j₁.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₁ ⁻¹ᵁ W) e = j₁.app _ ≫ Y₁.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_fst_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem fac₂ : j₂ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₂ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₂ hw hi₂ hj g₁ g₂ hg x
  · have hh : j₂.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₂ ⁻¹ᵁ W) e = j₂.app _ ≫ Y₂.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_snd_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem uniq (m : Y ⟶ T) (h₁ : j₁ ≫ m = g₁) (h₂ : j₂ ≫ m = g₂) : m = desc hw hi₂ hj hV g₁ g₂ hg := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    show m (j₁ x₁) = bse hj g₁ (j₁ x₁)
    rw [bse_j₁, ← h₁, Scheme.Hom.comp_apply]
  · rw [desc_app]
    apply (hV _).hom_ext
    · refine Eq.trans ?_ (liftApp_fst hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₁]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₁ _ _ _ _)
    · refine Eq.trans ?_ (liftApp_snd hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₂]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₂ _ _ _ _)

end Fac

theorem isPushout_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ →
    ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂),
    IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ →
    (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
      (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) →
    IsPushout i₁ i₂ j₁ j₂ := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ hs₂ Y j₁ j₂ hw hc₁ _ hs₁ _ hV
  have hj : IsHomeomorph j₁ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j₁.isClosedEmbedding.isEmbedding, hs₁.surj⟩
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => desc hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₁ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₂ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s m h₁ h₂ => uniq hw hs₂.surj hj hV s.inl s.inr s.condition m h₁ h₂))

end GlobalTheory.ThickPush
