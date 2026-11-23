import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchDeg

theorem elem_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y, f₁.hom x = f₁.hom y → f₂.hom x = f₂.hom y → x = y) ∧
      ∀ a b, g₁.hom a = g₂.hom b → ∃ x, f₁.hom x = a ∧ f₂.hom x = b := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H.2.1 x y ⟨hx, hy⟩, fun a b h ↦ H.2.2 a b h⟩

theorem subsingleton_or_subsingleton {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [IsLocalRing P] : Subsingleton R₁ ∨ Subsingleton R₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  obtain ⟨e, he₁, he₂⟩ := hex 1 0 (Subsingleton.elim _ _)
  have hidem : e * e = e := hinj _ _ (by simp [he₁]) (by simp [he₂])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · have h1 : e = 1 := by
      obtain ⟨u, rfl⟩ := hu
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hidem
    right
    rw [h1, map_one] at he₂
    exact subsingleton_of_zero_eq_one he₂.symm
  · have h0 : 1 - e = 1 := by
      have hid : (1 - e) * (1 - e) = 1 - e := by
        rw [sub_mul, one_mul, mul_sub, mul_one, hidem, sub_self, sub_zero]
      obtain ⟨u, hu⟩ := hu
      rw [← hu] at hid ⊢
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hid
    have he : e = 0 := by
      have := congrArg (fun t ↦ 1 - t) h0
      simpa using this
    left
    rw [he, map_zero] at he₁
    exact subsingleton_of_zero_eq_one he₁

theorem glue_of_subsingleton_right (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂)
    (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [Subsingleton R₂] (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀))
    (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left) (hY₁ : Flat Y₁.hom) :
    ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left),
      IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧
        Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  have hbij : Function.Bijective f₁.hom :=
    ⟨fun x y h ↦ hinj x y h (Subsingleton.elim _ _),
      fun a ↦ (hex a 0 (Subsingleton.elim _ _)).imp fun x hx ↦ hx.1⟩
  haveI : IsIso f₁ := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsEmpty (Spec R₂) := inferInstanceAs (IsEmpty (PrimeSpectrum R₂))
  haveI : IsEmpty Y₂.left := ⟨fun x ↦ isEmptyElim (Y₂.hom.base x)⟩
  haveI : IsEmpty Y₀.left := ⟨fun x ↦ isEmptyElim (i₂.base x)⟩
  let Y : Over (Spec P) := Over.mk (Y₁.hom ≫ Spec.map f₁)
  refine ⟨Y, 𝟙 _, isInitialOfIsEmpty.to _, ?_, ?_, ?_, ?_⟩
  · exact IsPullback.of_horiz_isIso ⟨by simp [Y]⟩
  · have hpb := IsPullback.of_hasPullback Y.hom (Spec.map f₂)
    haveI : IsEmpty ((pullback Y.hom (Spec.map f₂) : Scheme.{0})) :=
      ⟨fun x ↦ isEmptyElim ((pullback.snd Y.hom (Spec.map f₂)).base x)⟩
    let e : pullback Y.hom (Spec.map f₂) ≅ Y₂.left :=
      isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty
    refine IsPullback.of_iso hpb e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals first
      | exact isInitialOfIsEmpty.hom_ext _ _
      | simp
  · show Flat (Y₁.hom ≫ Spec.map f₁)
    infer_instance
  · haveI : IsIso i₂ := ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _⟩
    exact IsPushout.of_vert_isIso ⟨isInitialOfIsEmpty.hom_ext _ _⟩

theorem glue_of_subsingleton : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Subsingleton R₀ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP h₀ hloc _ _ _ Y₁ Y₂ Y₀ i₁ i₂ _ _ hY₁ hY₂
  rcases subsingleton_or_subsingleton hP with h₁ | h₂
  · obtain ⟨Y, j₂, j₁, hp₂, hp₁, hf, hpo⟩ :=
      glue_of_subsingleton_right P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip Y₂ Y₁ Y₀ i₂ i₁ hY₂
    exact ⟨Y, j₁, j₂, hp₁, hp₂, hf, hpo.flip⟩
  · exact glue_of_subsingleton_right P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP Y₁ Y₂ Y₀ i₁ i₂ hY₁

end GlobalTheory.PinchDeg
