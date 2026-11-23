import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.AffineCurveNbhd

theorem isNbhd_away_of_add_mul_eq_one (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A')
    (hN : IsNbhd B A' f) (hh : h + algebraMap B A' f * c = 1) : IsNbhd B (Localization.Away h) f := by
  set F := algebraMap B A' f with hF
  have hpow : ∀ m : ℕ, F ∣ h ^ m - 1 := by
    intro m
    have h1 : F ∣ h - 1 := ⟨-c, by linear_combination hh⟩
    have := sub_dvd_pow_sub_pow h 1 m
    rw [one_pow] at this
    exact h1.trans this
  have hL : ∀ b : B, algebraMap B (Localization.Away h) b =
      algebraMap A' (Localization.Away h) (algebraMap B A' b) := fun b =>
    IsScalarTower.algebraMap_apply B A' (Localization.Away h) b
  refine ⟨?_, ?_⟩
  · intro a'
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    rw [← hn] at hs
    obtain ⟨b, hb⟩ := hN.1 x
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨d, hd⟩ := hb
    refine ⟨b, ?_⟩
    rw [Ideal.mem_span_singleton, hL b, hL f]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv
    have hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1 := by
      refine ⟨algebraMap A' (Localization.Away h) c * u, ?_⟩
      have := congrArg (algebraMap A' (Localization.Away h)) hh
      simp only [map_add, map_mul, map_one] at this
      linear_combination hu - u * this
    have hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1 := by
      have := sub_dvd_pow_sub_pow u 1 n
      rw [one_pow] at this
      exact hu1.trans this
    obtain ⟨e, he⟩ := hun
    have ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n := by
      have : a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a' := by rw [hu, one_pow, mul_one]
      rw [← this, mul_pow, ← mul_assoc, ← map_pow, hs]
    refine ⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩
    have hx : algebraMap A' (Localization.Away h) x =
        algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F *
          algebraMap A' (Localization.Away h) d := by
      rw [← map_mul, ← map_add, ← hd]; ring_nf
    rw [ha']
    linear_combination (algebraMap A' (Localization.Away h) x) * he + hx
  · intro a ha
    rw [Ideal.mem_span_singleton, hL a, hL f] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    have heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) =
        algebraMap A' (Localization.Away h) (F * x) := by
      rw [map_mul, map_mul, hy, ← hs, hn]; ring
    obtain ⟨⟨k, hk⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hk
    simp only at hk'
    apply hN.2
    rw [Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hpow (m + n)
    refine ⟨h ^ m * x - g * algebraMap B A' a, ?_⟩
    rw [← hF]
    linear_combination hk' - algebraMap B A' a * hg

end GlobalTheory.AffineCurveNbhd
