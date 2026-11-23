import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayCont

open Asymptotics

section General

variable {E : ℝ → ℂ} {C : ℝ}

theorem mellin_indicator_eq (E : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ioi (1 : ℝ)).indicator E) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ioi (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans (Set.mem_Ioi.1 ht)))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul, Set.indicator_of_mem ht]
    rw [mul_comm]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]

theorem norm_indicator_le (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) (x : ℝ) :
    ‖(Set.Ioi (1 : ℝ)).indicator E x‖ ≤ ‖C * Real.sqrt x‖ := by
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem hx]
    exact (hC x (le_of_lt hx)).trans (Real.le_norm_self _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

theorem differentiableAt_integral (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1)) s := by
  have h : DifferentiableAt ℂ (mellin ((Set.Ioi (1 : ℝ)).indicator E)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 2)) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      have hc : Continuous fun x : ℝ => C * Real.sqrt x := by fun_prop
      exact hc.locallyIntegrable.mono (hE.indicator measurableSet_Ioi).aestronglyMeasurable
        (Eventually.of_forall (norm_indicator_le hC))
    · refine IsBigO.of_bound ‖C‖ (Eventually.of_forall fun t => ?_)
      refine (norm_indicator_le hC t).trans (le_of_eq ?_)
      rw [norm_mul, neg_neg, Real.sqrt_eq_rpow]
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      rw [Set.indicator_of_notMem (fun h => lt_asymm (Set.mem_Ioi.1 h) (Set.mem_Iio.1 ht))]
      simp
    · simp
  have := h.comp s differentiableAt_id.neg
  simp only [← mellin_indicator_eq]
  exact this

theorem norm_integrand_le (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) (s : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖E t * (t : ℂ) ^ (-s - 1)‖ ≤ C * t ^ (-(s.re + 1 / 2)) := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  refine (mul_le_mul_of_nonneg_right (hC _ (le_of_lt ht)) (Real.rpow_nonneg ht0.le _)).trans
    (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht0]
  congr 2
  simp only [sub_re, neg_re, one_re]
  ring

theorem integrableOn_integrand (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Set.Ioi (1 : ℝ)) := by
  have hlt : -(s.re + 1 / 2) < -1 := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_
    (norm_integrand_le hC s)
  exact (hE.mul (measurable_ofReal.pow_const _)).aestronglyMeasurable

theorem norm_integral_le (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ C / (s.re - 1 / 2) := by
  have hlt : -(s.re + 1 / 2) < -1 := by linarith
  refine (norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) (norm_integrand_le hC s)).trans ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
  refine le_of_eq ?_
  have : -(s.re + 1 / 2) + 1 = -(s.re - 1 / 2) := by ring
  rw [this, neg_div_neg_eq, mul_one_div]

end General

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

theorem res_eq : 𝓕.res χ = ∑ g, χ g * (𝓕.κ : ℂ) := by
  rw [← Finset.sum_mul, AddChar.sum_eq_ite, LFam.res, AddChar.one_eq_zero]
  split_ifs <;> simp [mul_comm]

theorem norm_rem_le (x : ℝ) (hx : 1 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by
  have h : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x =
      ∑ g, χ g * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.a g n - 𝓕.κ * x : ℝ) : ℂ) := by
    simp only [LFam.aChi, res_eq]
    rw [Finset.sum_comm, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ => 10 * Real.sqrt x) fun g _ => ?_).trans ?_
  · rw [norm_mul, AddChar.norm_apply, one_mul, norm_real, Real.norm_eq_abs]
    exact 𝓕.count g x hx
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right 𝓕.card_le (by positivity : 0 ≤ 10 * Real.sqrt x)
    linarith

theorem measurable_rem :
    Measurable fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x :=
  ((measurable_from_top (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, 𝓕.aChi χ n)).comp
    Nat.measurable_floor).sub (measurable_ofReal.const_mul _)

theorem differentiableAt_mel {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (𝓕.mel χ) s :=
  differentiableAt_integral (measurable_rem 𝓕 χ) (norm_rem_le 𝓕 χ) hs

theorem norm_mel_le {s : ℂ} (hs : 1 / 2 < s.re) : ‖𝓕.mel χ s‖ ≤ 10 * 𝓕.B / (s.re - 1 / 2) :=
  norm_integral_le (norm_rem_le 𝓕 χ) hs

theorem sum_norm_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖𝓕.aChi χ k‖) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Fintype.card 𝓕.G * 14) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.rpow_one, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ∀ k, ‖𝓕.aChi χ k‖ ≤ ∑ g, 𝓕.a g k := fun k => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => le_of_eq ?_)
    rw [norm_mul, AddChar.norm_apply, one_mul, norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g k)]
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum (g := fun _ => 14 * (n : ℝ)) fun g _ => ?_).trans (le_of_eq ?_)
  · have h := (abs_le.1 (𝓕.count g n hn1)).2
    rw [Nat.floor_natCast] at h
    have h2 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have h3 : 𝓕.κ * n ≤ 4 * n := mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

theorem LSeries_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (𝓕.aChi χ) s = s * (𝓕.mel χ s + 𝓕.res χ / (s - 1)) := by
  rw [LSeries_eq_mul_integral' _ zero_le_one hs (sum_norm_isBigO 𝓕 χ)]
  congr 1
  have hlt : (-s).re < -1 := by simpa using hs
  have h1 : ∫ t in Set.Ioi (1 : ℝ), 𝓕.res χ * (t : ℂ) ^ (-s) = 𝓕.res χ / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hlt zero_lt_one]
    have : -s + 1 = -(s - 1) := by ring
    rw [ofReal_one, one_cpow, this, neg_div_neg_eq, mul_one_div]
  rw [← h1, LFam.mel, ← integral_add
    (integrableOn_integrand (measurable_rem 𝓕 χ) (norm_rem_le 𝓕 χ) (by linarith))
    ((integrableOn_Ioi_cpow_of_lt hlt zero_lt_one).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (zero_lt_one.trans ht).ne'
  have h2 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-s - 1) := by
    rw [cpow_sub _ _ ht0, cpow_one]
    field_simp
  have h3 : -(s + 1) = -s - 1 := by ring
  rw [h2, h3]
  ring

theorem norm_res_le : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B := by
  have hB := 𝓕.B_ge
  have hκ : 0 ≤ 𝓕.κ := le_trans (by positivity) 𝓕.κ_ge
  rw [LFam.res]
  split_ifs
  · rw [norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
  · rw [norm_zero]
    positivity

theorem conj_res : (starRingEnd ℂ) (𝓕.res χ) = 𝓕.res χ := by
  rw [LFam.res]
  split_ifs
  · exact conj_ofReal _
  · exact map_zero _

theorem conj_aChi (h : χ * χ = 1) (n : ℕ) : (starRingEnd ℂ) (𝓕.aChi χ n) = 𝓕.aChi χ n := by
  rw [LFam.aChi, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : χ g * χ g = 1 := by
    have := DFunLike.congr_fun h g
    simpa using this
  rw [map_mul, conj_ofReal]
  rcases mul_self_eq_one_iff.1 h1 with h2 | h2 <;> simp [h2]

theorem mel_conj (h : χ * χ = 1) (s : ℂ) :
    𝓕.mel χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.mel χ s) := by
  rw [LFam.mel, LFam.mel, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := zero_lt_one.trans ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_ne_zero.symm
  have h1 : (t : ℂ) ^ (-(starRingEnd ℂ) s - 1) = (starRingEnd ℂ) ((t : ℂ) ^ (-s - 1)) := by
    have := cpow_conj (t : ℂ) (-s - 1) harg
    rw [conj_ofReal, map_sub, map_neg, map_one] at this
    exact this
  simp only [map_mul, map_sub, map_sum, conj_aChi 𝓕 χ h, conj_res, conj_ofReal, h1]

theorem continuation_growth : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  intro 𝓕 χ
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩, fun s hs => ?_, fun h s => ?_⟩
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
      (isOpen_lt continuous_const continuous_re)
    have hm := differentiableAt_mel 𝓕 χ hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold LFam.F
    split_ifs <;> fun_prop
  · exact LSeriesSummable_of_sum_norm_bigO (sum_norm_isBigO 𝓕 χ) zero_le_one hs
  · have hs1 : s - 1 ≠ 0 := fun h => by
      rw [sub_eq_zero.1 h] at hs
      simp at hs
    rw [LSeries_eq 𝓕 χ hs, LFam.F]
    split_ifs with h
    · field_simp
      ring
    · simp [LFam.res, h]
  · have hB := 𝓕.B_ge
    have hm : ‖𝓕.mel χ s‖ ≤ 200 * 𝓕.B := by
      refine (norm_mel_le 𝓕 χ (by linarith)).trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hr := norm_res_le 𝓕 χ
    have h0 := norm_nonneg s
    have h1 : ‖s * 𝓕.mel χ s‖ ≤ ‖s‖ * (200 * 𝓕.B) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hm h0
    have hBs : 0 ≤ 𝓕.B * ‖s‖ := by positivity
    have hBs2 : 0 ≤ 𝓕.B * ‖s‖ ^ 2 := by positivity
    rw [LFam.F]
    split_ifs
    · have h2 : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
      have h3 : ‖(s - 1) * s * 𝓕.mel χ s‖ ≤ (‖s‖ + 1) * (‖s‖ * (200 * 𝓕.B)) := by
        rw [mul_assoc, norm_mul]
        exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      have h4 : ‖𝓕.res χ * s‖ ≤ 4 * 𝓕.B * ‖s‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hr h0
      refine (norm_add_le _ _).trans ?_
      nlinarith
    · nlinarith
  · rw [LFam.F, LFam.F, mel_conj 𝓕 χ h]
    split_ifs <;> simp [conj_res]

end GlobalTheory.Hk.RayCont
