import Mathlib

theorem GlobalTheory.away_congr_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  intro A C _ _ _ f g hfg hC c'
  obtain ⟨u, v, huv⟩ := hfg
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) c'
  obtain ⟨k, hk⟩ := s.2
  obtain ⟨a, ha⟩ := hC c
  refine ⟨algebraMap A (Localization.Away f) (a * u ^ k), ?_⟩
  have hmap : ∀ x : A, Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) x)
      = algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C x) :=
    fun x => IsLocalization.map_eq _ _
  rw [hmap, hmap]
  rw [Ideal.mem_span_singleton] at ha ⊢
  have hunit : IsUnit (algebraMap C (Localization.Away (algebraMap A C f)) (s : C)) :=
    IsLocalization.map_units _ s
  rw [← hunit.dvd_mul_right]
  have key : (IsLocalization.mk' (Localization.Away (algebraMap A C f)) c s
      - algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C (a * u ^ k)))
      * algebraMap C (Localization.Away (algebraMap A C f)) (s : C)
      = algebraMap C (Localization.Away (algebraMap A C f)) (c - algebraMap A C (a * (u * f) ^ k)) := by
    rw [sub_mul, IsLocalization.mk'_spec, ← hk]
    simp only [map_sub, map_mul, map_pow]
    ring
  rw [key]
  apply map_dvd
  have h1 : g ∣ a * (1 - (u * f) ^ k) := by
    have h2 : g ∣ 1 - u * f := ⟨v, by rw [← huv]; ring⟩
    have h3 : 1 - u * f ∣ 1 ^ k - (u * f) ^ k := sub_dvd_pow_sub_pow 1 (u * f) k
    rw [one_pow] at h3
    exact Dvd.dvd.mul_left (h2.trans h3) a
  have h4 := map_dvd (algebraMap A C) h1
  have : c - algebraMap A C (a * (u * f) ^ k) = (c - algebraMap A C a) + algebraMap A C (a * (1 - (u * f) ^ k)) := by
    simp only [map_sub, map_mul, map_pow, map_one]; ring
  rw [this]
  exact dvd_add ha h4
