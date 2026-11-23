import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PinchUnits

open ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem pushout_sec_exists {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s₁ : Γ(X₁, ⊤)) (s₂ : Γ(X₂, ⊤))
    (h : i₁.appTop.hom s₁ = i₂.appTop.hom s₂) :
    ∃ s : Γ(X, ⊤), j₁.appTop.hom s = s₁ ∧ j₂.appTop.hom s = s₂ := by
  have w : i₁ ≫ mOf s₁ = i₂ ≫ mOf s₂ := by rw [comp_mOf, comp_mOf, h]
  refine ⟨fnOf (H.desc (mOf s₁) (mOf s₂) w), ?_, ?_⟩
  · rw [← fnOf_comp, H.inl_desc, fnOf_mOf]
  · rw [← fnOf_comp, H.inr_desc, fnOf_mOf]

theorem pushout_sec_ext {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s s' : Γ(X, ⊤))
    (h₁ : j₁.appTop.hom s = j₁.appTop.hom s') (h₂ : j₂.appTop.hom s = j₂.appTop.hom s') : s = s' := by
  apply mOf_inj
  apply H.hom_ext
  · rw [comp_mOf, comp_mOf, h₁]
  · rw [comp_mOf, comp_mOf, h₂]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem isPullback_resLE_self {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) (f ⁻¹ᵁ U).ι U.ι f := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict f U

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hc hc₂
  have hle : ∀ U : Y.left.Opens, i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U) ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ U) := by
    intro U x hx
    have e : (i₁ ≫ j₁) x = (i₂ ≫ j₂) x := by rw [hc]
    show j₂ (i₂ x) ∈ U
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hx
  have key : ∀ U : Y.left.Opens,
      (∀ (s₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)) (s₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)),
        (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom s₁ =
          (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom s₂ →
        ∃ d : Γ(Y.left, U), (j₁.app U).hom d = s₁ ∧ (j₂.app U).hom d = s₂) ∧
      (∀ d d' : Γ(Y.left, U), (j₁.app U).hom d = (j₁.app U).hom d' →
        (j₂.app U).hom d = (j₂.app U).hom d' → d = d') := by
    intro U
    let V₁ := j₁ ⁻¹ᵁ U
    let V₂ := j₂ ⁻¹ᵁ U
    let V₀ := i₁ ⁻¹ᵁ V₁
    let k₁ := j₁.resLE U V₁ le_rfl
    let k₂ := j₂.resLE U V₂ le_rfl
    let l₁ := i₁.resLE V₁ V₀ le_rfl
    let l₂ := i₂.resLE V₂ V₀ (hle U)
    have pb1 : IsPullback k₁ (V₁.ι ≫ Y₁.hom) (U.ι ≫ Y.hom) (Spec.map f₁) :=
      (isPullback_resLE_self j₁ U).paste_vert h₁
    have pb2 : IsPullback k₂ (V₂.ι ≫ Y₂.hom) (U.ι ≫ Y.hom) (Spec.map f₂) :=
      (isPullback_resLE_self j₂ U).paste_vert h₂
    have pb0 : IsPullback l₁ (V₀.ι ≫ Y₀.hom) (V₁.ι ≫ Y₁.hom) (Spec.map g₁) :=
      (isPullback_resLE_self i₁ V₁).paste_vert h₀
    have e1 : l₁ ≫ k₁ = l₂ ≫ k₂ := by
      rw [← cancel_mono U.ι]
      simp only [k₁, k₂, l₁, l₂, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hc]
    have e2 : l₂ ≫ (V₂.ι ≫ Y₂.hom) = (V₀.ι ≫ Y₀.hom) ≫ Spec.map g₂ := by
      simp only [l₂, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, hc₂]
    have hfl' : Flat (Over.mk (U.ι ≫ Y.hom)).hom := by
      haveI := hfl
      show Flat (U.ι ≫ Y.hom)
      infer_instance
    have H : IsPushout l₁ l₂ k₁ k₂ :=
      GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (U.ι ≫ Y.hom))
        (Over.mk (V₁.ι ≫ Y₁.hom)) (Over.mk (V₂.ι ≫ Y₂.hom)) (Over.mk (V₀.ι ≫ Y₀.hom)) k₁ k₂ l₁ l₂
        hfl' pb1 pb2 pb0 e1 e2
    have hj : ∀ d : Γ(Y.left, U), k₁.appTop.hom (U.topIso.inv.hom d) = V₁.topIso.inv.hom ((j₁.app U).hom d) ∧
        k₂.appTop.hom (U.topIso.inv.hom d) = V₂.topIso.inv.hom ((j₂.app U).hom d) := fun d =>
      ⟨(resLE_appTop_topIso_inv j₁ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE]),
       (resLE_appTop_topIso_inv j₂ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE])⟩
    refine ⟨fun s₁ s₂ h => ?_, fun d d' e₁ e₂ => ?_⟩
    · obtain ⟨t, ht1, ht2⟩ := pushout_sec_exists H (V₁.topIso.inv.hom s₁) (V₂.topIso.inv.hom s₂)
        (by rw [resLE_appTop_topIso_inv, resLE_appTop_topIso_inv, h])
      refine ⟨U.topIso.hom.hom t, ?_, ?_⟩
      · have := congrArg V₁.topIso.hom.hom ((hj (U.topIso.hom.hom t)).1)
        rwa [Iso.hom_inv_id_apply, ht1, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
      · have := congrArg V₂.topIso.hom.hom ((hj (U.topIso.hom.hom t)).2)
        rwa [Iso.hom_inv_id_apply, ht2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
    · have := pushout_sec_ext H (U.topIso.inv.hom d) (U.topIso.inv.hom d')
        (by rw [(hj d).1, (hj d').1, e₁]) (by rw [(hj d).2, (hj d').2, e₂])
      have := congrArg U.topIso.hom.hom this
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  refine ⟨fun U a₁ a₂ hg => ?_, fun U d d' e₁ e₂ => Units.ext ((key U).2 d.val d'.val
    (congrArg Units.val e₁) (congrArg Units.val e₂))⟩
  have heq : ∀ (b₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (b₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ),
      (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) b₁ = gm i₂ x (j₂ ⁻¹ᵁ U) b₂) →
      (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom b₁.val =
        (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom b₂.val := by
    intro b₁ b₂ hb
    apply TopCat.Presheaf.section_ext Y₀.left.sheaf
    intro x hx
    have := congrArg Units.val (hb x hx)
    rw [gm_val i₁ x _ hx, gm_val i₂ x _ (hle U hx)] at this
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact this
  obtain ⟨d, hd1, hd2⟩ := (key U).1 a₁.val a₂.val (heq a₁ a₂ hg)
  obtain ⟨d', hd1', hd2'⟩ := (key U).1 (a₁⁻¹).val (a₂⁻¹).val (heq a₁⁻¹ a₂⁻¹ (fun x hx => by
    rw [map_inv, map_inv, hg x hx]))
  have hdd : d * d' = 1 := (key U).2 _ _ (by rw [map_mul, map_one, hd1, hd1', Units.mul_inv])
    (by rw [map_mul, map_one, hd2, hd2', Units.mul_inv])
  exact ⟨⟨d, d', hdd, by rw [mul_comm, hdd]⟩, Units.ext hd1, Units.ext hd2⟩

end GlobalTheory.PinchUnits
