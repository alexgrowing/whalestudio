import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.PinchPoints

theorem ring_lift_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (a : R₁) (b : R₂)
    (hab : g₁ a = g₂ b) : ∃ x : P, f₁ x = a ∧ f₂ x = b :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.2 a b hab

theorem ring_ext_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (x y : P)
    (h₁ : f₁ x = f₁ y) (h₂ : f₂ x = f₂ y) : x = y :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.1 x y ⟨h₁, h₂⟩

theorem scheme_exists_of_isPullback {X Y Z W : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ w, fst w = x ∧ snd w = y := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]

theorem closedImmersion_of_isPullback {W X Y Z : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsClosedImmersion g] :
    IsClosedImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance

theorem spec_subsingleton_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] :
    Subsingleton (Spec P) :=
  ⟨fun a b => PrimeSpectrum.ext
    ((IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ a.asIdeal a.isPrime _)).trans
      (IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ b.asIdeal b.isPrime _)).symm)⟩

theorem spec_nonempty_iff (R : CommRingCat.{0}) : Nonempty (Spec R) ↔ Nontrivial R := by
  rw [← not_isEmpty_iff, ← not_subsingleton_iff_nontrivial]
  exact not_congr (PrimeSpectrum.isEmpty_iff_subsingleton (R := R))

theorem points_of_pinch : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Y₁ Y₂ Y₀ : Scheme.{0}) (p : Y ⟶ Spec P) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback j₁ p₁ p (Spec.map f₁) → IsPullback j₂ p₂ p (Spec.map f₂) → IsPullback i₁ p₀ p₁ (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) ∧ ∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → ∃ y₀ : Y₀, i₁ y₀ = y₁ ∧ i₂ y₀ = y₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ p p₁ p₂ p₀ j₁ j₂ i₁ i₂ h₁ h₂ h₀ hcomm
  have hf₁ : Function.Surjective f₁ := fun a => by
    obtain ⟨b, hb⟩ := hg₂ (g₁ a)
    obtain ⟨x, hx, -⟩ := ring_lift_of_isPullback hP a b hb.symm
    exact ⟨x, hx⟩
  have hf₂ : Function.Surjective f₂ := fun b => by
    obtain ⟨a, ha⟩ := hg₁ (g₂ b)
    obtain ⟨x, -, hx⟩ := ring_lift_of_isPullback hP a b ha
    exact ⟨x, hx⟩
  haveI := IsClosedImmersion.spec_of_surjective f₁ hf₁
  haveI := IsClosedImmersion.spec_of_surjective f₂ hf₂
  haveI : IsClosedImmersion j₁ := closedImmersion_of_isPullback h₁
  haveI : IsClosedImmersion j₂ := closedImmersion_of_isPullback h₂
  haveI : Subsingleton (Spec P) := spec_subsingleton_of_artinian P
  haveI : Subsingleton (Spec R₁) := (Spec.map f₁).isClosedEmbedding.injective.subsingleton
  have lift₁ : Nontrivial R₁ → ∀ y : Y, ∃ y₁, j₁ y₁ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₁).2 hn
    obtain ⟨y₁, hy, -⟩ := scheme_exists_of_isPullback h₁ y s (Subsingleton.elim _ _)
    exact ⟨y₁, hy⟩
  have lift₂ : Nontrivial R₂ → ∀ y : Y, ∃ y₂, j₂ y₂ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₂).2 hn
    obtain ⟨y₂, hy, -⟩ := scheme_exists_of_isPullback h₂ y s (Subsingleton.elim _ _)
    exact ⟨y₂, hy⟩
  refine ⟨fun y => ?_, fun y₁ y₂ hy => ?_⟩
  · by_cases hn : Nontrivial R₁
    · exact Or.inl (lift₁ hn y)
    · by_cases hn₂ : Nontrivial R₂
      · exact Or.inr (lift₂ hn₂ y)
      · exfalso
        rw [not_nontrivial_iff_subsingleton] at hn hn₂
        exact one_ne_zero (ring_ext_of_isPullback hP (1 : P) 0 (Subsingleton.elim _ _)
          (Subsingleton.elim _ _))
  · have hn₁ : Nontrivial R₁ := (spec_nonempty_iff R₁).1 ⟨p₁ y₁⟩
    have hn₂ : Nontrivial R₂ := (spec_nonempty_iff R₂).1 ⟨p₂ y₂⟩
    have hn₀ : Nontrivial R₀ := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      obtain ⟨e, he₁, he₂⟩ := ring_lift_of_isPullback hP (1 : R₁) (0 : R₂) (Subsingleton.elim _ _)
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · have h' := hu.map f₂.hom
        rw [show f₂.hom e = 0 from he₂] at h'
        exact not_isUnit_zero h'
      · have h' := hu.map f₁.hom
        rw [map_sub, map_one, show f₁.hom e = 1 from he₁, sub_self] at h'
        exact not_isUnit_zero h'
    obtain ⟨s₀⟩ := (spec_nonempty_iff R₀).2 hn₀
    obtain ⟨y₀, hy₀, -⟩ := scheme_exists_of_isPullback h₀ y₁ s₀ (Subsingleton.elim _ _)
    refine ⟨y₀, hy₀, j₂.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, hy₀, hy]

end GlobalTheory.PinchPoints
