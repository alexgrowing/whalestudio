import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnfoldingOperatorConditions

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.IntegralPowerExpansion

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram depthSub)

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_q {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) :
    P.valuation E (qOf P : E) = WithZero.exp (-1) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : P.intValuation (qOf P : 𝓞 E) < 1 :=
    (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have h2 : ¬ P.intValuation (qOf P : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact hP.2
  have hx : P.intValuation (qOf P : 𝓞 E) ≠ 0 := by
    intro h0
    exact h2 (h0 ▸ zero_le)
  rw [← WithZero.exp_log hx] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  omega

theorem q_ne_zero {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hP.1.ne_zero

theorem exists_int_add_q_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {u : E} (hu : IntAt P u) :
    ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) * u' := by
  obtain ⟨r, s, hs, h⟩ := hu
  haveI : Fact (qOf P).Prime := ⟨hP.1⟩
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    rw [qOf, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
    (mem_zmultiples_of_prime_card (g' := Ideal.Quotient.mk P.asIdeal r) hc (mk_ne_zero hs))
  have hm : r - k * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_intCast, ← hk, zsmul_eq_mul, sub_self]
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  have h2 : algebraMap (𝓞 E) E s * (u - k) = algebraMap (𝓞 E) E (r - k * s) := by
    rw [map_sub, map_mul, map_intCast, ← h]; ring
  have h3 : P.valuation E (u - k) < 1 := by
    have := congrArg (P.valuation E) h2
    rw [map_mul, h1, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    rw [this]
    exact (P.intValuation_lt_one_iff_mem _).2 hm
  have hq := q_ne_zero hP
  refine ⟨k, (u - k) / qOf P, ?_, by field_simp; ring⟩
  rw [intAt_iff_val, map_div₀, val_q hP]
  exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one h3) zero_le

theorem exists_int_add_q_pow_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (j : ℕ) {u : E}
    (hu : IntAt P u) : ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) ^ j * u' := by
  induction j with
  | zero => exact ⟨0, u, hu, by simp⟩
  | succ j ih =>
    obtain ⟨k, u', hu', e⟩ := ih
    obtain ⟨k', u'', hu'', e'⟩ := exists_int_add_q_mul hP hu'
    refine ⟨k + (qOf P : ℤ) ^ j * k', u'', hu'', ?_⟩
    rw [e, e']
    push_cast
    ring

end GlobalTheory.Proof.IntegralPowerExpansion
