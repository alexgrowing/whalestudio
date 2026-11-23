import Mathlib
import Formalism.PeriodIntegrals.UnipVal

open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UnipVal.Main

open PI.UnipVal

variable {K : Type} [Field K] [NumberField K]

lemma vw_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vw w (x * y) = vw w x + vw w y := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hx)
      (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hy)]

lemma vw_pow (w : HeightOneSpectrum (𝓞 K)) (x : K) (k : ℕ) : vw w (x ^ k) = k * vw w x := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

lemma vw_int_eq_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0)
    (hxw : x ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K x) = 0 := by
  have hJ : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  have h0 : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {x})).factors = 0 := by
    by_contra hne
    exact hxw ((Ideal.span_singleton_le_iff_mem _).mp
      (Ideal.le_of_dvd ((Associates.count_ne_zero_iff_dvd hJ w.irreducible).mp hne)))
  simp only [vw]
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  exact_mod_cast h0

lemma plc_prime (w : HeightOneSpectrum (𝓞 K)) : (plc w).Prime := by
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : w.asIdeal.IsPrime := w.isPrime
  rw [plc]
  exact CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _

lemma natCast_mem_iff (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ((m : 𝓞 K) ∈ w.asIdeal) ↔ plc w ∣ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, plc, ringChar.spec]

theorem part1 (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≠ 0) :
    vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ) := by
  have hp := plc_prime w
  haveI : Fact (plc w).Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := plc w) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hpm : ¬ plc w ∣ m := by
    rintro ⟨c, rfl⟩
    exact pow_succ_padicValNat_not_dvd hn ⟨c, hm.trans (by ring)⟩
  have hmw : ((m : 𝓞 K)) ∉ w.asIdeal := by
    rw [natCast_mem_iff]
    exact hpm
  have hm0' : ((m : 𝓞 K)) ≠ 0 := by
    intro h
    apply hmw
    rw [h]
    exact w.asIdeal.zero_mem
  have hval := vw_int_eq_zero w (m : 𝓞 K) hm0' hmw
  rw [map_natCast] at hval
  have hpK : ((plc w : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmK : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  conv_lhs => rw [hm]
  rw [Nat.cast_mul, Nat.cast_pow, vw_mul w (pow_ne_zero _ hpK) hmK, vw_pow, hval, ramw]
  ring

lemma pv_prime (l g : ℕ) (hl : l.Prime) (hg : g.Prime) :
    padicValNat l g = if l = g then 1 else 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  split_ifs with h
  · rw [h]
    exact padicValNat.self hg.one_lt
  · exact padicValNat.eq_zero_of_not_dvd fun hd => h ((Nat.prime_dvd_prime_iff_eq hl hg).mp hd)

theorem part2 (w : HeightOneSpectrum (𝓞 K)) (g₁ g₂ a : ℕ) (h1 : g₁.Prime) (h2 : g₂.Prime)
    (h12 : g₁ ≠ g₂) :
    (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) =
      (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0) := by
  have hp := plc_prime w
  haveI : Fact (plc w).Prime := ⟨hp⟩
  have ha1 : g₁ ^ a ≠ 0 := pow_ne_zero _ h1.ne_zero
  have ha2 : g₂ ^ a ≠ 0 := pow_ne_zero _ h2.ne_zero
  rw [part1 w _ (mul_ne_zero ha1 ha2), padicValNat.mul ha1 ha2, padicValNat.pow g₁ a,
    padicValNat.pow g₂ a, pv_prime _ _ hp h1, pv_prime _ _ hp h2]
  by_cases e1 : plc w = g₁
  · have e2 : plc w ≠ g₂ := fun e => h12 (e1.symm.trans e)
    rw [if_pos e1, if_neg e2, if_pos (Or.inl e1)]
    push_cast
    ring
  · by_cases e2 : plc w = g₂
    · rw [if_neg e1, if_pos e2, if_pos (Or.inr e2)]
      push_cast
      ring
    · rw [if_neg e1, if_neg e2, if_neg (not_or.mpr ⟨e1, e2⟩)]
      push_cast
      ring

end PI.UnitaryGroupMassFormula.UnipVal.Main

end
