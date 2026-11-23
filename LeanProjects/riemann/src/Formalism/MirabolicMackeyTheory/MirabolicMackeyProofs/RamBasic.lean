import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsChain
import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem plc_prime (w : HeightOneSpectrum (𝓞 K)) : (plc w).Prime := by
  haveI := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  unfold plc
  exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ w.asIdeal) _)

theorem plc_mem (w : HeightOneSpectrum (𝓞 K)) : ((plc w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  unfold plc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

private theorem vw_coe_eq_count_factors_span_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (𝓞 K))).factors : ℤ) := by
  have hspan : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.count_coe K w hspan, FractionalIdeal.coeIdeal_span_singleton]

theorem intValuation_eq_exp' (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_coe_eq_count_factors_span_of_ne_zero w x hx, IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hx]

theorem one_le_ramw (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ ramw w := by
  have hm := plc_mem w
  have hne : ((plc w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (plc_prime w).ne_zero
  have h1 := (w.intValuation_lt_one_iff_mem _).mpr hm
  rw [intValuation_eq_exp' w _ hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ramw
  push_cast at h1
  omega

theorem plc_conjPl (w : HeightOneSpectrum (𝓞 K)) : plc (conjPl w) = plc w := by
  unfold plc
  let e := Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl
  haveI := ringChar.charP (𝓞 K ⧸ w.asIdeal)
  haveI : CharP (𝓞 K ⧸ (conjPl w).asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) :=
    charP_of_injective_ringHom (f := (e : 𝓞 K ⧸ w.asIdeal →+* 𝓞 K ⧸ (conjPl w).asIdeal))
      e.injective _
  exact ringChar.eq _ _

theorem ramw_conjPl (w : HeightOneSpectrum (𝓞 K)) : ramw (conjPl w) = ramw w := by
  unfold ramw
  rw [plc_conjPl, ← (valuation_basic_properties K w).2.1 ((plc w : ℕ) : K), star_natCast]

theorem sum_lw_vw_natCast_le (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have hd0 : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  have hI0 : (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hn0

  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, ∀ w, e w =
      (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {((n : ℕ) : 𝓞 K)})).factors :=
    ⟨_, fun _ => rfl⟩
  have hv : ∀ w, vw w (n : K) = (e w : ℤ) := by
    intro w
    have h := vw_coe_eq_count_factors_span_of_ne_zero w _ hn0
    rw [he w]
    have hc : (((n : ℕ) : 𝓞 K) : K) = (n : K) := by
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    rw [hc] at h
    exact h

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hn0, he w]
  have hdvd : ∏ w ∈ T, w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      show IsCoprime (a.asIdeal ^ e a) (b.asIdeal ^ e b)
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne a.isMaximal b.isMaximal
        (fun h => hab (HeightOneSpectrum.ext h))
    · intro w _
      exact hdiv w
  have hP0 : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact hI0 hdvd
  have hle : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≤
      Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) := by
    apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
      exact hI0
    · exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  have hnormI : Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) =
      n ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)) n,
      Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    intro w
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast this
  have hlog : Real.log (Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) : ℝ) =
      ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    rw [map_prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro w _
      rw [map_pow, Nat.cast_pow]
      exact pow_ne_zero _ (hNw w)
  have hlogle : ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) ≤
      (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    rw [← hlog, ← Real.log_pow, ← Nat.cast_pow, ← hnormI]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hP0
    · exact_mod_cast hle
  have hsum : ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) =
      (∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hv w]
    unfold lw
    push_cast
    ring
  rw [hsum, div_le_iff₀ hd0, mul_comm (Real.log (n : ℝ))]
  exact hlogle

end SlopeTestRemainingChoices

theorem ramified_basic_bound : RamBasic := by
  unfold RamBasic
  intro K _ _ _ w
  refine ⟨plc_prime w, one_le_ramw w, plc_conjPl w, ramw_conjPl w, ?_⟩
  have h1 : (1:ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast one_le_ramw w
  have hp : (0:ℝ) < (plc w : ℝ) := by exact_mod_cast (plc_prime w).pos
  unfold ellw
  rw [div_pow, Real.sq_sqrt (by linarith)]
  have h2 : (ramw w : ℝ) ≠ 0 := by linarith
  have h3 : (plc w : ℝ) ≠ 0 := hp.ne'
  first
    | (field_simp; ring)
    | field_simp

theorem place_sum : PlaceSum := by
  unfold PlaceSum
  intro K _ _ _ S X hX
  rw [← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem plc hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : p ≠ 0 := by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hp
    rw [← hw]
    exact (plc_prime w).ne_zero
  have e : ∑ w ∈ S with plc w = p, lw w * ((ramw w : ℝ) * X (plc w)) =
      (∑ w ∈ S with plc w = p, lw w * (vw w (p : K) : ℝ)) * X p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h4 : plc w = p := (Finset.mem_filter.mp hw).2
    unfold ramw
    rw [h4]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sum_lw_vw_natCast_le _ p hp0) (hX p)

end Formalism.EigenvalueLevelCeiling
