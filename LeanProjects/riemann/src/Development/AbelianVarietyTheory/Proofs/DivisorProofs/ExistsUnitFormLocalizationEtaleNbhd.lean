import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC

namespace GlobalTheory.DivUnitForm

private lemma exists_sub_mem_span_pow_of_surj_mod_span {B A₂ : Type} [CommRing B] [CommRing A₂] [Algebra B A₂]
    (f : B) (hsurj : ∀ a' : A₂, ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f})
    (n : ℕ) (a' : A₂) : ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f ^ n} := by
  induction n generalizing a' with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih a'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨a₁, ha₁⟩ := hsurj r
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 ha₁
    refine ⟨a + f ^ n * a₁, Ideal.mem_span_singleton'.2 ⟨s, ?_⟩⟩
    have hr' : a' = r * algebraMap B A₂ f ^ n + algebraMap B A₂ a := by rw [hr]; ring
    have hs' : r = s * algebraMap B A₂ f + algebraMap B A₂ a₁ := by rw [hs]; ring
    rw [hr', hs', map_add, map_mul, map_pow]
    ring

theorem _root_.GlobalTheory.DivUnitForm.unit_form : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂]
    [Algebra B A₂] (f : B), _root_.GlobalTheory.EtC.IsExcisionNbhd B A₂ f →
    ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂),
      e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) =
        (c : Localization.Away (algebraMap B A₂ f)) *
          algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  intro B A₂ _ _ _ f hf c
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    (c : Localization.Away (algebraMap B A₂ f))
  obtain ⟨l, y, hy⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
  have hxy : algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (x * y) =
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f ^ (k + l)) := by
    rw [map_mul, ← hx, ← hy, map_pow, pow_add]
    have hc : (c : Localization.Away (algebraMap B A₂ f)) *
        ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
          = 1 := Units.mul_inv c
    linear_combination (algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
      (algebraMap B A₂ f) ^ k * algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
        (algebraMap B A₂ f) ^ l) * hc
  obtain ⟨⟨s, hs⟩, hsxy⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap B A₂ f))
    (Localization.Away (algebraMap B A₂ f))).1 hxy
  obtain ⟨N, rfl⟩ := hs
  simp only at hsxy
  set X := x * algebraMap B A₂ f ^ N with hX
  have hXy : X * y = algebraMap B A₂ f ^ (k + N + l) := by
    rw [hX, show k + N + l = N + (k + l) by ring, pow_add]
    linear_combination hsxy
  obtain ⟨b, hb⟩ := exists_sub_mem_span_pow_of_surj_mod_span f hf.2.1 (k + N + l + 1) X
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b, k + N, 1 - algebraMap B A₂ f * y * r, Ideal.mem_span_singleton'.2 ⟨-(y * r), by ring⟩, ?_⟩
  have hbX : algebraMap B A₂ b = X * (1 - algebraMap B A₂ f * y * r) := by
    have h1 : X * (1 - algebraMap B A₂ f * y * r) = X - algebraMap B A₂ f * r * (X * y) := by ring
    rw [h1, hXy]
    linear_combination hr
  rw [hbX, hX]
  simp only [map_mul, map_pow]
  rw [← hx]
  ring

end GlobalTheory.DivUnitForm
