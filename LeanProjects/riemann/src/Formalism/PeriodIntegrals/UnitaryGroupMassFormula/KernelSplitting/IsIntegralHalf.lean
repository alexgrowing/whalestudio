import Mathlib
import Formalism.PeriodIntegrals.SelfDualOfDiff

noncomputable section
open NumberField Polynomial

namespace PI.UnitaryGroupMassFormula.KerSplit

theorem isIntegral_sqrt {K : Type} [Field K] (d : ℕ) (s : K) (hs : s * s = -(d : K)) :
    IsIntegral ℤ s := by
  refine ⟨X ^ 2 + C (d : ℤ), monic_X_pow_add_C _ two_ne_zero, ?_⟩
  have e : (algebraMap ℤ K) (d : ℤ) = (d : K) := by simp
  rw [eval₂_add, eval₂_X_pow, eval₂_C, e]
  linear_combination hs

theorem isIntegral_half {K : Type} [Field K] [CharZero K] (d : ℕ) (s : K) (hd : d % 8 = 7)
    (hs : s * s = -(d : K)) : IsIntegral ℤ ((1 + s) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hkK : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), ?_, ?_⟩
  · have e : (X ^ 2 - X + C (k : ℤ) : ℤ[X]) = X ^ 2 - (X - C (k : ℤ)) := by ring
    rw [e]
    apply monic_X_pow_sub
    rw [degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr (by norm_num)
  · have e : (algebraMap ℤ K) (k : ℤ) = (k : K) := by simp
    rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, e]
    linear_combination (1 / 4 : K) * hs - (1 / 4 : K) * hkK

private theorem exists_isPrime_natCast_mem {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    rintro ⟨v, hv⟩
    have h1 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) * (p : K) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 K) K) p, ← map_mul, ← hv, Units.inv_mul, map_one]
    have h2 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) = algebraMap ℚ K ((p : ℚ)⁻¹) := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left h1
    have hint : IsIntegral ℤ (algebraMap ℚ K ((p : ℚ)⁻¹)) := by
      rw [← h2]
      exact RingOfIntegers.isIntegral_coe _
    have hq : IsIntegral ℤ ((p : ℚ)⁻¹) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K) (algebraMap ℚ K).injective).1 hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hn' : (n : ℚ) = (p : ℚ)⁻¹ := by simpa using hn
    have h4 : ((n * p : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hn']
      exact inv_mul_cancel₀ hp0
    have h5 : n * (p : ℤ) = 1 := by exact_mod_cast h4
    have h6 : (p : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact h5.symm⟩
    have h7 := Int.eq_one_of_dvd_one (by positivity) h6
    have h8 : p = 1 := by exact_mod_cast h7
    exact hp.one_lt.ne' h8
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact ⟨M, hM.isPrime, hle (Ideal.subset_span (Set.mem_singleton _))⟩

theorem splitsAt_two {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d : ℕ) (s : K) (hd : d % 8 = 7) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) : PI.KerIso.SplitsAt K cj 2 := by
  obtain ⟨P, hP, h2P⟩ := exists_isPrime_natCast_mem (K := K) 2 Nat.prime_two
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 8 * m := ⟨(d + 1) / 8, by omega⟩
  have hmK : (d : K) + 1 = 8 * (m : K) := by exact_mod_cast hm
  obtain ⟨aO, haK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + s) / 2 :=
    ⟨⟨_, isIntegral_half d s hd hs⟩, rfl⟩
  obtain ⟨bO, hbK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + -s) / 2 :=
    ⟨⟨_, isIntegral_half d (-s) hd (by rw [neg_mul_neg]; exact hs)⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hsum : aO + bO = 1 := hinj (by rw [map_add, haK, hbK, map_one]; ring)
  have hprod : aO * bO = ((2 : ℕ) : 𝓞 K) * (m : 𝓞 K) := hinj (by
    rw [map_mul, haK, hbK, map_mul, map_natCast, map_natCast]
    push_cast
    linear_combination (-1 / 4 : K) * hs + (1 / 4 : K) * hmK)
  have hca : cj (algebraMap K E ((1 + s) / 2)) = algebraMap K E ((1 + -s) / 2) := by
    simp only [map_div₀, map_add, map_neg, map_one, map_ofNat, hcj]
  have hcb : cj (algebraMap K E ((1 + -s) / 2)) = algebraMap K E ((1 + s) / 2) := by
    simp only [map_div₀, map_add, map_neg, map_one, map_ofNat, hcj, neg_neg]
  have hab : aO * bO ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2P
  have hcoe : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, h2P, aO, bO, ?_, ha, fun hb => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hca
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb
  · refine ⟨P, hP, h2P, bO, aO, ?_, hb, fun ha => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hcb
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb

theorem splitsAt_odd {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : jacobiSym (-(d : ℤ)) p = 1) : PI.KerIso.SplitsAt K cj p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hpP⟩ := exists_isPrime_natCast_mem (K := K) p hp
  obtain ⟨r, t, ht⟩ : ∃ r t : ℤ, r * r + (d : ℤ) = (p : ℤ) * t := by
    obtain ⟨c, hc⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ (c.val : ℤ) * (c.val : ℤ) + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      push_cast at hc
      linear_combination -hc
    exact ⟨_, t, ht⟩
  have hg : Int.gcd (-(d : ℤ)) (p : ℤ) = 1 := by
    by_contra h
    have h0 := (jacobiSym.eq_zero_iff_not_coprime (a := -(d : ℤ)) (b := p)).2 h
    rw [hJ] at h0
    exact one_ne_zero h0
  obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.2 hg
  obtain ⟨sO, hsK⟩ : ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = s := ⟨⟨s, isIntegral_sqrt d s hs⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hss : sO * sO = -((d : ℕ) : 𝓞 K) :=
    hinj (by rw [map_mul, hsK, map_neg, map_natCast]; exact hs)
  have hprod : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) = ((p : ℕ) : 𝓞 K) * (t : 𝓞 K) := by
    have h1 : ((r * r + d : ℤ) : 𝓞 K) = ((p * t : ℤ) : 𝓞 K) := by rw [ht]
    push_cast at h1
    linear_combination h1 - hss
  have hab : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ hpP
  have hnot : ¬ ((r : 𝓞 K) + sO ∈ P ∧ (r : 𝓞 K) - sO ∈ P) := by
    rintro ⟨h1, h2⟩
    have h2s : (2 : 𝓞 K) * sO ∈ P := by
      have h3 := P.sub_mem h1 h2
      rwa [show (r : 𝓞 K) + sO - ((r : 𝓞 K) - sO) = 2 * sO by ring] at h3
    obtain ⟨q, hq⟩ := hp.odd_of_ne_two hp2
    have hc' : (((q + 1 : ℕ)) : 𝓞 K) * 2 = ((p : ℕ) : 𝓞 K) + 1 := by
      rw [hq]
      push_cast
      ring
    have hsP : sO ∈ P := by
      have e : sO = (((q + 1 : ℕ)) : 𝓞 K) * (2 * sO) - sO * ((p : ℕ) : 𝓞 K) := by
        linear_combination (-sO) * hc'
      rw [e]
      exact P.sub_mem (P.mul_mem_left _ h2s) (P.mul_mem_left _ hpP)
    have hdP : ((d : ℕ) : 𝓞 K) ∈ P := by
      have h4 := P.mul_mem_left sO hsP
      rw [hss] at h4
      exact (P.neg_mem_iff).1 h4
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : 𝓞 K) = ((x : ℤ) : 𝓞 K) * (-((d : ℕ) : 𝓞 K)) + (y : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
      have h5 := congrArg (fun z : ℤ => (z : 𝓞 K)) hxy
      push_cast at h5
      exact h5.symm
    rw [e1]
    exact P.add_mem (P.mul_mem_left _ (P.neg_mem hdP)) (P.mul_mem_left _ hpP)
  have hca : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO)) := by
    simp only [map_add, map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg]
  have hcb : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO)) := by
    simp only [map_add, map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg, neg_neg]
  have hcoe : ∀ z : 𝓞 K, (z : K) = algebraMap (𝓞 K) K z := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, hpP, (r : 𝓞 K) + sO, (r : 𝓞 K) - sO, ?_, ha, fun hb => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hca
  · refine ⟨P, hP, hpP, (r : 𝓞 K) - sO, (r : 𝓞 K) + sO, ?_, hb, fun ha => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hcb

end PI.UnitaryGroupMassFormula.KerSplit
