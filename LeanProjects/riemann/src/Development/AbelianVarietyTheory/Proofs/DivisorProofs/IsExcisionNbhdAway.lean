import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A),
    IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} →
      IsExcisionNbhd A (Localization.Away a) h := by
  intro A A' _ _ _ h ⟨hE, hS, hI⟩ a b hab
  have hpow : ∀ n : ℕ, a ^ n * b ^ n - 1 ∈ Ideal.span {algebraMap A A' h} := by
    intro n
    have hd : a * b - 1 ∣ (a * b) ^ n - 1 ^ n := sub_dvd_pow_sub_pow _ _ _
    rw [one_pow, mul_pow] at hd
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right _ _ hab
  have hH : algebraMap A (Localization.Away a) h =
      algebraMap A' (Localization.Away a) (algebraMap A A' h) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hmap : ∀ x : A', x ∈ Ideal.span {algebraMap A A' h} →
      algebraMap A' (Localization.Away a) x ∈ Ideal.span {algebraMap A (Localization.Away a) h} := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [hH, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · haveI := hE
    haveI : Algebra.Etale A' (Localization.Away a) := inferInstance
    exact Algebra.Etale.comp A A' (Localization.Away a)
  · intro z
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) z
    obtain ⟨n, hn⟩ := s.2
    obtain ⟨c, hc⟩ := hS (y * b ^ n)
    refine ⟨c, ?_⟩
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have e1 : IsLocalization.mk' (Localization.Away a) y s - algebraMap A (Localization.Away a) c =
        -(IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n * b ^ n - 1)) +
          algebraMap A' (Localization.Away a) (y * b ^ n - algebraMap A A' c) := by
      rw [map_sub, map_sub, map_mul, map_mul, map_one, ← hs, ← IsScalarTower.algebraMap_apply]
      ring
    rw [e1]
    exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hmap _ (hpow n)))) (hmap _ hc)
  · intro x hx
    apply hI
    rw [hH] at hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) w
    obtain ⟨n, hn⟩ := s.2
    dsimp only at hw
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have key : algebraMap A' (Localization.Away a) (algebraMap A A' x * a ^ n - y * algebraMap A A' h) = 0 := by
      rw [map_sub, map_mul, map_mul, ← hs, ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) x, ← hw,
        ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) h]
      ring
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 key
    obtain ⟨N, hN⟩ := m.2
    have h1 : algebraMap A A' x * a ^ (N + n) ∈ Ideal.span {algebraMap A A' h} := by
      have e : algebraMap A A' x * a ^ (N + n) = (a ^ N * y) * algebraMap A A' h := by
        rw [← hN] at hm; rw [pow_add]; linear_combination hm
      rw [e]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have e2 : algebraMap A A' x = algebraMap A A' x * a ^ (N + n) * b ^ (N + n) -
        algebraMap A A' x * (a ^ (N + n) * b ^ (N + n) - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ (hpow _))

end GlobalTheory.EtC
