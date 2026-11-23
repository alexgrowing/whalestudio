import Mathlib

namespace GlobalTheory

theorem padicInt_toZModPow_not_dvd_mul :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e →
      ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) →
        ¬ ((l : ℤ) ^ N ∣ e * m) := by
  intro l _ c hc e he
  have hl : l.Prime := Fact.out
  refine ⟨c.valuation + e.factorization l + 1, ?_⟩
  intro m hm hdvd
  set v := c.valuation with hv
  set a := e.factorization l with ha
  have hm1 : (l : ℤ) ^ (v + 1) ∣ m := by
    have he' : (e : ℤ) = (l : ℤ) ^ a * ((e / l ^ a : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self e l).symm
    have hcop : IsCoprime ((l : ℤ) ^ (v + 1)) ((e / l ^ a : ℕ) : ℤ) := by
      have h := (Nat.coprime_ordCompl hl he.ne').pow_left (v + 1)
      have := Nat.isCoprime_iff_coprime.mpr h
      simpa [Nat.cast_pow] using this
    rw [he', show v + a + 1 = a + (v + 1) by ring, pow_add, mul_assoc] at hdvd
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero a (by exact_mod_cast hl.ne_zero : (l : ℤ) ≠ 0))).mp hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have h0 : PadicInt.toZModPow (v + 1) c = 0 := by
    rw [← PadicInt.cast_toZModPow (v + 1) (v + a + 1) (by omega) c, hm,
      ZMod.cast_intCast (pow_dvd_pow l (by omega))]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm1
  have hmem : c ∈ (Ideal.span {(l : ℤ_[l]) ^ (v + 1)} : Ideal ℤ_[l]) := by
    rw [← PadicInt.ker_toZModPow]
    exact h0
  have := (PadicInt.mem_span_pow_iff_le_valuation c hc (v + 1)).mp hmem
  omega

end GlobalTheory
