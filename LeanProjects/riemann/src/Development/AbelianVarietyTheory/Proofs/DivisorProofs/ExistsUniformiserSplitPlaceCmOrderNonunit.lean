import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOneStatement

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem span_sup_pow_eq_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {x : R}
    (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) (n : ℕ) : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal := by
  have hd : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ∣ v.asIdeal ^ (n + 1) := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow v.prime _).1 hd
  rw [associated_iff_eq] at hi
  have hle : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ≤ v.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) (Ideal.pow_le_self (by omega))
  have hxi : x ∈ v.asIdeal ^ i := hi ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  rw [hi] at hle ⊢
  match i, hle, hxi with
  | 0, hle, _ => exact absurd (top_le_iff.1 (by simpa using hle)) v.isPrime.ne_top
  | 1, _, _ => exact pow_one _
  | i + 2, _, hxi => exact absurd (Ideal.pow_le_pow_right (by omega) hxi) hx2

theorem eq_exp_neg_one_of_le_of_not_le {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by
  have h0 : g ≠ 0 := fun h => h2 (h ▸ zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

theorem locIn_succ_nonunit_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  intro E _ _ _ v hv
  have he := fun P hP => ((GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv).2 P hP).2.1
  obtain ⟨x, hx1, hx2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have hval : ∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ) := fun P hP =>
    eq_exp_neg_one_of_le_of_not_le (by simpa using val_iota_le_of_mem hP 1 hx1)
      (fun h => hx2 ((he P hP x 2).1 ((val_iota_le_iff P 2 x).1 (by simpa using h))))
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨x, hval, fun n π y hπ => ?_⟩
  have hx0 : ∀ P, Over P v → iota x P ≠ 0 := fun P hP h => by
    have := hval P hP
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hq : ∀ P, Over P v → ((π⁻¹ * y : (Af E)ˣ) : Af E) P = (iota x P)⁻¹ * (y : Af E) P := fun P hP => by
    rw [Units.val_mul, mul_coord, inv_coord, hπ P hP]
  constructor
  · intro h
    refine ⟨?_, fun hu => ?_⟩
    · obtain ⟨b, hb⟩ := h
      refine ⟨x * b, fun P hP => ?_⟩
      have h0 := hx0 P hP
      have : (y : Af E) P - iota (x * b) P = iota x P * (((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P) := by
        rw [hq P hP, iota_mul, mul_coord]; field_simp
      rw [this, map_mul, hval P hP]
      refine (mul_le_mul' le_rfl (hb P hP)).trans_eq ?_
      rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · obtain ⟨P, -, -, hP, -⟩ := hv
      have h1 := h.val_le hP
      rw [hq P hP, map_mul, map_inv₀, hval P hP, hu P hP, mul_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h1
      omega
  · rintro ⟨h, hu⟩
    push Not at hu
    obtain ⟨Q, hQ, hyQ⟩ := hu
    have hyQ' : Valued.v ((y : Af E) Q) < 1 := lt_of_le_of_ne (h.val_le hQ) hyQ
    obtain ⟨a, ha⟩ := h
    have hav : a ∈ v.asIdeal := by
      have h2 : Valued.v ((y : Af E) Q - iota a Q) < 1 :=
        ((ha Q hQ).trans (WithZero.exp_le_exp.2 (by push_cast; omega))).trans_lt hlt
      have h3 := Valuation.map_sub_lt _ hyQ' h2
      rw [sub_sub_cancel] at h3
      have h4 : Valued.v (iota a Q) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
        by_cases h0 : Valued.v (iota a Q) = 0
        · rw [h0]; exact zero_le'
        · rw [← WithZero.exp_log h0] at h3 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          rw [WithZero.exp_le_exp]; push_cast; omega
      simpa using (he Q hQ a 1).1 ((val_iota_le_iff Q 1 a).1 h4)
    rw [← span_sup_pow_eq_of_notMem_sq v (by simpa using hx1) hx2 n] at hav
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hav
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine ⟨b, fun P hP => ?_⟩
    have h0 := hx0 P hP
    have : ((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P =
        (iota x P)⁻¹ * (((y : Af E) P - iota (b * x + t) P) + iota t P) := by
      rw [hq P hP, iota_add, iota_mul, add_coord, mul_coord]; field_simp; ring
    rw [this, map_mul, map_inv₀, hval P hP]
    refine (mul_le_mul' le_rfl (Valuation.map_add_le _ (ha P hP) (val_iota_le_of_mem hP (n + 1) ht))).trans_eq ?_
    rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.CMVal.Euler
