import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDiscStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLargeVonMangoldtLogPowerSeriesNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeMeanOfLargeDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.LogFree

theorem principal_height : ∃ η : ℝ, 0 < η ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 - η ≤ s.re → s.re < 1 →
    LFunction (1 : DirichletCharacter ℂ q) s = 0 → 3 ≤ |s.im| := by
  obtain ⟨c, hc, H⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 2) (c / Real.log 5), by positivity, fun q _ s h1 h2 h0 => ?_⟩
  have hs : s ≠ 1 := by rintro rfl; simp at h2
  have hre : 0 < s.re := by have := min_le_left (1 / 2 : ℝ) (c / Real.log 5); linarith
  have hz : riemannZeta s = 0 := by
    have h := LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs
    rw [LFunctionTrivChar, h0] at h
    rcases mul_eq_zero.1 h.symm with h | h
    · exfalso
      obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.1 h
      have hpp := Nat.prime_of_mem_primeFactors hp
      have h3 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by simpa using hre)
      rw [← sub_eq_zero.1 hp0] at h3
      simp at h3
    · exact h
  have := H 1 s hs (by rw [LFunction_modOne_eq]; exact hz)
  by_contra hlt
  push Not at hlt
  have hl : Real.log ((1 : ℕ) * (|s.im| + 2)) ≤ Real.log 5 :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have hl0 : 0 < Real.log ((1 : ℕ) * (|s.im| + 2)) :=
    Real.log_pos (by have := abs_nonneg s.im; push_cast; linarith)
  have h4 : c / Real.log 5 ≤ c / Real.log ((1 : ℕ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hl0 hl
  have := min_le_right (1 / 2 : ℝ) (c / Real.log 5)
  linarith

theorem count_le (Z : Finset ℂ) (w : ℂ → ℝ) (F : ℝ → ℝ) (U h δ M : ℝ) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hZ : ∀ ρ ∈ Z, |ρ.im| + h ≤ U)
    (hF : IntervalIntegrable F volume (-U) U) (hF0 : ∀ τ, 0 ≤ F τ)
    (h1 : ∀ ρ ∈ Z, ∀ τ, |τ - ρ.im| ≤ h → δ ≤ F τ ∧
      ∑ z ∈ Z.filter (fun z => |τ - z.im| ≤ h), w z ≤ M) :
    δ * (2 * h) * ∑ ρ ∈ Z, w ρ ≤ M * ∫ τ in (-U)..U, F τ := by
  have hU' : -U ≤ U := by linarith
  set g : ℂ → ℝ → ℝ := fun ρ => (Set.Icc (ρ.im - h) (ρ.im + h)).indicator (fun _ => δ * w ρ) with hg
  have hgi : ∀ ρ, IntegrableOn (g ρ) (Set.Icc (-U) U) := fun ρ =>
    (integrableOn_const (by simp)).indicator measurableSet_Icc
  have hint : ∀ ρ ∈ Z, ∫ τ in Set.Icc (-U) U, g ρ τ = δ * (2 * h) * w ρ := by
    intro ρ hρ
    have := hZ ρ hρ
    have h2 := le_abs_self ρ.im
    have h3 := neg_abs_le ρ.im
    rw [hg]
    simp only
    rw [setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_self_of_subset_right (Set.Icc_subset_Icc (by linarith) (by linarith))]
    simp only [setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [Finset.mul_sum, ← Finset.sum_congr rfl hint, ← integral_finset_sum _ (fun ρ _ => hgi ρ),
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hU',
    ← integral_Icc_eq_integral_Ioc]
  refine integral_mono (integrable_finset_sum _ (fun ρ _ => hgi ρ)) ?_ fun τ => ?_
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hU').1 hF).const_mul M
  · have he : ∑ ρ ∈ Z, g ρ τ = δ * ∑ z ∈ Z.filter (fun z => |τ - z.im| ≤ h), w z := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [hg, Set.indicator, Set.mem_Icc]
      congr 1
      rw [abs_le]
      apply propext
      constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
    simp only
    rw [he]
    rcases (Z.filter (fun z => |τ - z.im| ≤ h)).eq_empty_or_nonempty with h0 | ⟨ρ, hρ⟩
    · rw [h0]; simpa using mul_nonneg hM (hF0 τ)
    · obtain ⟨a, b⟩ := Finset.mem_filter.1 hρ
      obtain ⟨c, d⟩ := h1 ρ a τ b
      calc _ ≤ δ * M := mul_le_mul_of_nonneg_left d hδ
        _ ≤ F τ * M := mul_le_mul_of_nonneg_right c hM
        _ = _ := mul_comm _ _

noncomputable def primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N y τ : ℝ) : ℂ :=
  ∑ p ∈ primesIoc N y, ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I))

theorem norm_cpow_le (n : ℕ) (τ : ℝ) : ‖(n : ℂ) ^ (-(τ * I))‖ ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · by_cases h : (-(τ * I) : ℂ) = 0
    · rw [h]; simp
    · rw [Nat.cast_zero, Complex.zero_cpow h]; simp
  · rw [Complex.norm_natCast_cpow_of_pos hn]; simp

theorem integrable_primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N M T : ℝ) (hN : 1 ≤ N) :
    Integrable (Function.uncurry fun τ y : ℝ => ‖primeSum χ N y τ‖ ^ 2 / y)
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioc N M))) := by
  have hm1 : Measurable (fun x : ℝ × ℕ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ x.2).filter Nat.Prime,
      ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(x.1 * I))) := by
    refine measurable_from_prod_countable_left fun n => ?_
    show Measurable (fun τ : ℝ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ n).filter Nat.Prime,
      ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I)))
    refine Continuous.measurable (continuous_finsetSum _ fun p hp => ?_)
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hp0))
  have hm0 : Measurable (fun x : ℝ × ℝ => ((x.1, ⌊x.2⌋₊) : ℝ × ℕ)) :=
    measurable_fst.prodMk (Nat.measurable_floor.comp measurable_snd)
  have hm2 : Measurable (fun x : ℝ × ℝ => primeSum χ N x.2 x.1) := by
    have := hm1.comp hm0
    simpa only [Function.comp_def, primeSum, primesIoc] using this
  have hm3 : Measurable (Function.uncurry fun τ y : ℝ => ‖primeSum χ N y τ‖ ^ 2 / y) :=
    (hm2.norm.pow_const 2).div measurable_snd
  refine Integrable.of_bound hm3.aestronglyMeasurable
    ((∑ p ∈ primesIoc N M, ‖(Real.log p : ℂ) / p‖) ^ 2) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mono ?_
  rintro ⟨τ, y⟩ ⟨-, hy1, hy2⟩
  simp only at hy1 hy2
  have hb : ‖primeSum χ N y τ‖ ≤ ∑ p ∈ primesIoc N M, ‖(Real.log p : ℂ) / p‖ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _))
    · rw [norm_mul, norm_mul, mul_assoc]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_cpow_le p τ))
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hy2))
  simp only [Function.uncurry]
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) (by linarith))]
  exact (div_le_self (by positivity) (by linarith)).trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

theorem sum_log_div_le : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ N y : ℝ, 1 ≤ y →
    ∑ p ∈ primesIoc N y, (p : ℝ) * ‖(Real.log p : ℂ) / p‖ ^ 2 / Real.log p ≤ Real.log y + CM := by
  obtain ⟨CM, h0, H⟩ := GlobalTheory.mertens_first_vonMangoldt
  refine ⟨CM, h0, fun N y hy => ?_⟩
  have h1 := (abs_le.1 (H y hy)).2
  have : ∑ p ∈ primesIoc N y, (p : ℝ) * ‖(Real.log p : ℂ) / p‖ ^ 2 / Real.log p ≤
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) := by
    refine (le_of_eq (Finset.sum_congr rfl fun p hp => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => Λ n / (n : ℝ)) ?_
        fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    · have hpp := (Finset.mem_filter.1 hp).2
      have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      rw [vonMangoldt_apply_prime hpp, norm_div, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg hl.le]
      field_simp
    · intro p hp
      have := Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1
      exact Finset.mem_Icc.2 ⟨by omega, this.2⟩
  linarith

theorem mean_le : ∃ C CM : ℝ, 0 < C ∧ 0 ≤ CM ∧ ∀ (q : ℕ) [NeZero q] (T N M : ℝ), 1 ≤ T → 1 ≤ N → N ≤ M →
    (2 * q * T) ^ 2 ≤ N →
    ∑ χ : DirichletCharacter ℂ q, (∫ τ in (-T)..T, ∫ y in N..M, ‖primeSum χ N y τ‖ ^ 2 / y) ≤
      C * (Real.log M + CM) * Real.log M := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.primeMeanValue_characters_twist_integral_le
  obtain ⟨CM, hCM, HM⟩ := sum_log_div_le
  refine ⟨C, CM, hC, hCM, fun q _ T N M hT hN hNM hq => ?_⟩
  have hT' : -T ≤ T := by linarith
  simp only [intervalIntegral.integral_of_le hT', intervalIntegral.integral_of_le hNM]
  have hI := fun χ : DirichletCharacter ℂ q => integrable_primeSum χ N M T hN
  simp only [fun χ => integral_integral_swap (hI χ)]
  have hJ : ∀ χ : DirichletCharacter ℂ q, Integrable (fun y : ℝ =>
      ∫ τ in Set.Ioc (-T) T, ‖primeSum χ N y τ‖ ^ 2 / y) (volume.restrict (Set.Ioc N M)) :=
    fun χ => (hI χ).integral_prod_right
  rw [← integral_finset_sum _ (fun χ _ => hJ χ)]
  have hlM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hc : IntegrableOn (fun y : ℝ => C * (Real.log M + CM) * y⁻¹) (Set.Ioc N M) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => by
      have := hy.1; simp only [id]; linarith)
  calc _ ≤ ∫ y in Set.Ioc N M, C * (Real.log M + CM) * y⁻¹ := by
        refine setIntegral_mono_on (integrable_finset_sum _
          (fun χ _ => hJ χ)) hc measurableSet_Ioc fun y hy => ?_
        have hy1 : 1 ≤ y := by linarith [hy.1]
        simp only [integral_div]
        rw [← Finset.sum_div, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 := H q T N y (fun p => (Real.log p : ℂ) / p) hT hq
        simp only [intervalIntegral.integral_of_le hT'] at h1
        refine h1.trans (mul_le_mul_of_nonneg_left ((HM N y hy1).trans ?_) hC.le)
        have := Real.log_le_log (by linarith) hy.2
        linarith
    _ = C * (Real.log M + CM) * Real.log (M / N) := by
        rw [← intervalIntegral.integral_of_le hNM, intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by linarith) (by linarith)]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) (by linarith))
          (div_le_self (by linarith) hN)) (by positivity)

theorem derSeries_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (x τ : ℝ) :
    derSeries (fun n : ℕ => χ (n : ZMod q)) k ((x : ℝ) + τ * I) =
      derSeries (fun n : ℕ => χ (n : ZMod q) * (n : ℂ) ^ (-(τ * I))) k (x : ℝ) := by
  unfold derSeries
  refine tsum_congr fun n => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
    ring

theorem finite_zerosBox {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (T : ℝ) (hσ : 0 < σ) :
    (zerosBox χ σ T).Finite :=
  (GlobalTheory.Mem.An.ZeroWindow.finite_zeros χ 0 T).subset fun _ h =>
    ⟨hσ.trans_le h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2⟩

theorem detect : ∃ a b C C' r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) →
      Real.log (q * (|τ| + 2)) ≤ L → 0 < r → 1 / L ≤ r → r ≤ r₀ → C' * r * L ≤ K → K₀ ≤ K →
      LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r →
      Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)),
        ‖primeSum χ (Real.exp (a * K / r)) y τ‖ ^ 2 / y := by
  obtain ⟨A, C3, r3, hA, hC3, hr3, H3⟩ := GlobalTheory.T.exists_large_vonMangoldtLogPowerSeries_near_zero
  obtain ⟨a, b, C4, r4, K0, ha, hab, hC4, hr4, H4⟩ := GlobalTheory.T.integral_prime_sum_sq_ge_of_derSeries_large A hA
  refine ⟨a, b, C4, C3, min r3 r4, K0, ha, hab, hC4, hC3, lt_min hr3 hr4, ?_⟩
  intro q _ χ τ r L K ρ h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨k, k1, k2, k3⟩ := H3 q χ τ r L K ρ h1 h2 h4 (h5.trans (min_le_left _ _)) h6 h8 h9
  rw [derSeries_twist] at k3
  have := H4 _ r K k (fun n => by
    rw [norm_mul]; exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_cpow_le n τ))
    h3 (h5.trans (min_le_right _ _)) h7 k1 k2 k3
  refine this.trans (le_of_eq ?_)
  congr 1
  ext y
  unfold primeSum
  congr 3
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem near {ρ : ℂ} {σ r τ : ℝ} (h1 : σ ≤ ρ.re) (h2 : ρ.re < 1) (h3 : 2 * (1 - σ) ≤ r)
    (h4 : |τ - ρ.im| ≤ r / 2) : ‖ρ - (1 + τ * I)‖ ≤ r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (ρ - (1 + τ * I)).re = ρ.re - 1 := by simp
  have e2 : (ρ - (1 + τ * I)).im = ρ.im - τ := by simp
  rw [e1, e2, abs_sub_comm ρ.im, abs_of_neg (by linarith)]
  linarith

theorem count_param : ∃ a D C C' r₀ K₀ η : ℝ, 0 < a ∧ 0 < D ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧ 0 < η ∧
    ∀ (q : ℕ) [NeZero q] (T σ r L : ℝ) (K : ℕ), 2 ≤ T → 1 - η ≤ σ → 2 * (1 - σ) ≤ r → 0 < r →
      r ≤ r₀ → 1 / L ≤ r → Real.log (q * (T + 3)) ≤ L → C' * r * L ≤ K → K₀ ≤ K → 1 ≤ K →
      (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) →
      ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤
        D * (1 + r * L) * Real.exp (C * K) * (K : ℝ) ^ 2 := by
  obtain ⟨η, hη, H1⟩ := principal_height
  obtain ⟨C2, hC2, H2⟩ := GlobalTheory.T.dirichletL_few_zeros_small_disc
  obtain ⟨a, b, C4, C3, r0, K0, ha, hab, hC4, hC3, hr0, H3⟩ := detect
  obtain ⟨C5, CM, hC5, hCM, H5⟩ := mean_le
  have hb : 0 < b := ha.trans hab
  refine ⟨a, C2 * C5 * (b + CM) * b, C4, C3, min (1 / 2) r0, K0, η, ha, by positivity, hC4, hC3,
    by positivity, hη, ?_⟩
  intro q _ T σ r L K hT hσ hσr hr hrr hL hqL hK3 hK0 hK1 hN
  have hr2 : r ≤ 1 / 2 := hrr.trans (min_le_left _ _)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hL0 : 0 ≤ L := (Real.log_nonneg (by nlinarith)).trans hqL
  set N := Real.exp (a * K / r) with hNdef
  set M := Real.exp (b * K / r) with hMdef
  have hN1 : 1 ≤ N := Real.one_le_exp (by positivity)
  have hNM : N ≤ M := Real.exp_le_exp.2 (by gcongr)
  have hmean := H5 q (T + 1) N M (by linarith) hN1 hNM hN
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      Real.exp (-(C4 * K)) / r ^ 3 * (2 * (r / 2)) * (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤
      C2 * (1 + r * L) * ∫ τ in (-(T + 1))..(T + 1), ∫ y in N..M, ‖primeSum χ N y τ‖ ^ 2 / y := by
    intro χ
    have hfin := finite_zerosBox χ (σ := σ) T (by linarith)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine count_le _ _ _ _ _ _ _ (by positivity) (by linarith) (by positivity) (by positivity)
      (fun ρ hρ => ?_) ?_ (fun τ => ?_) (fun ρ hρ τ hτ => ?_)
    · have := (hfin.mem_toFinset.1 hρ).2.2.1
      linarith
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      simp only [intervalIntegral.integral_of_le hNM]
      exact (integrable_primeSum χ N M (T + 1) hN1).integral_prod_left
    · exact intervalIntegral.integral_nonneg hNM fun y hy =>
        div_nonneg (by positivity) (by linarith [hy.1])
    · obtain ⟨z1, z2, z3, z4⟩ := hfin.mem_toFinset.1 hρ
      have t1 := abs_sub_abs_le_abs_sub τ ρ.im
      have t2 := abs_sub_abs_le_abs_sub ρ.im τ
      rw [abs_sub_comm] at t2
      have hc : χ ≠ 1 ∨ 2 ≤ |τ| := by
        by_cases h : χ = 1
        · subst h
          have := H1 q ρ (by linarith) z2 z4
          right; linarith
        · exact Or.inl h
      have hlog : Real.log (q * (|τ| + 2)) ≤ L :=
        (Real.log_le_log (by positivity) (by gcongr ?_ * ?_; linarith)).trans hqL
      refine ⟨H3 q χ τ r L K ρ hc hlog hr hL (hrr.trans (min_le_right _ _)) hK3 hK0 z4
        (near z1 z2 hσr hτ), ?_⟩
      obtain ⟨f1, f2⟩ := H2 q χ τ r hc hr hr2
      rw [finsum_mem_eq_finite_toFinset_sum _ f1] at f2
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _)
        (f2.trans (by gcongr))
      intro z hz
      obtain ⟨y0, y5⟩ := Finset.mem_filter.1 hz
      obtain ⟨y1, y2, -, y4⟩ := hfin.mem_toFinset.1 y0
      refine f1.mem_toFinset.2 ⟨near y1 y2 hσr y5, Or.inr ?_, y4⟩
      rintro rfl
      simp at y2
  have hsum := Finset.sum_le_sum fun χ (_ : χ ∈ Finset.univ) => hchar χ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hMdef, Real.log_exp] at hmean
  have h6 := hsum.trans (mul_le_mul_of_nonneg_left hmean (by positivity))
  generalize (∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) = S at h6 ⊢
  have he := Real.exp_pos (C4 * K)
  have h7 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ Real.exp (C4 * K) * r ^ 2 by positivity)
  rw [Real.exp_neg] at h7
  calc S = Real.exp (C4 * K) * r ^ 2 * ((Real.exp (C4 * K))⁻¹ / r ^ 3 * (2 * (r / 2)) * S) := by
        field_simp
    _ ≤ _ := h7
    _ = C2 * C5 * (b * K + CM * r) * b * (1 + r * L) * Real.exp (C4 * K) * K := by
        field_simp
    _ ≤ C2 * C5 * (b * K + CM * K) * b * (1 + r * L) * Real.exp (C4 * K) * K := by
        gcongr; linarith
    _ = _ := by ring

theorem zero_density : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 - η ≤ σ → σ ≤ 1 → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  obtain ⟨a, D, C, C3, r0, K0, η, ha, hD, hC, hC3, hr0, hη, H⟩ := count_param
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = C3 + |K0| + 4 / a := ⟨_, rfl⟩
  have hK0 := abs_nonneg K0
  have h4a : 0 < 4 / a := by positivity
  have hE0 : 0 < E := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (E + 1) + 3 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨6 * B, D * (E + 1) ^ 2 * Real.exp (2 * B), min η (r0 / 2), by positivity, by positivity,
    by positivity, fun q _ T σ hT hσ hσ1 => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have m1 := min_le_left η (r0 / 2)
  have m2 := min_le_right η (r0 / 2)
  have hl0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hir : 0 < 1 / r0 := by positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (q * (T + 3)) + 1 / r0 := ⟨_, rfl⟩
  have hL0 : 0 < L := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max (2 * (1 - σ)) (1 / L) := ⟨_, rfl⟩
  have r1 : 2 * (1 - σ) ≤ r := hr ▸ le_max_left _ _
  have r2 : 1 / L ≤ r := hr ▸ le_max_right _ _
  have r3 : 0 < r := lt_of_lt_of_le (by positivity) r2
  have r4 : r ≤ r0 := by
    rw [hr]
    refine max_le (by linarith) ?_
    rw [div_le_comm₀ hL0 hr0]; linarith
  have x1 : 1 ≤ r * L := (div_le_iff₀ hL0).1 r2
  have hlT : Real.log (q * (T + 3)) ≤ 3 * Real.log (q * T) := by
    have hT2 : 4 ≤ T ^ 2 := by nlinarith
    have h3 : T + 3 ≤ T ^ 3 := by nlinarith
    have h4 : (q : ℝ) ≤ q ^ 3 := le_self_pow₀ hq (by norm_num)
    calc _ ≤ Real.log ((q * T) ^ 3) := by
          refine Real.log_le_log (by positivity) ?_
          rw [mul_pow]; gcongr
      _ = _ := by rw [Real.log_pow]; norm_num
  have x2 : r * L ≤ 2 + 6 * (1 - σ) * Real.log (q * T) := by
    have s0 : 0 ≤ 1 - σ := by linarith
    have s1 : 2 * (1 - σ) * (1 / r0) ≤ 1 := by
      rw [mul_one_div, div_le_one hr0]; linarith
    have s2 := mul_le_mul_of_nonneg_left hlT s0
    have s3 := mul_nonneg s0 hl0
    rcases max_choice (2 * (1 - σ)) (1 / L) with h | h
    · rw [hr, h, hL]; nlinarith
    · rw [hr, h, one_div_mul_cancel hL0.ne']; nlinarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈E * (r * L)⌉₊ := ⟨_, rfl⟩
  have k1 : E * (r * L) ≤ K := hK ▸ Nat.le_ceil _
  have k2 : (K : ℝ) ≤ (E + 1) * (r * L) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ E * (r * L) by positivity)
    rw [← hK] at this
    linarith
  have k3 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) k1
    exact_mod_cast this
  have hN : (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) := by
    have n1 : 4 * L ≤ a * K / r := by
      rw [le_div_iff₀ r3]
      have : 4 / a * (r * L) ≤ K := le_trans (by gcongr; linarith) k1
      have := mul_le_mul_of_nonneg_left this ha.le
      calc 4 * L * r = a * (4 / a * (r * L)) := by field_simp
        _ ≤ _ := this
    have n2 : 2 * q * (T + 1) ≤ (q * (T + 3)) ^ 2 := by
      have : (q : ℝ) ≤ q ^ 2 := by nlinarith
      have : 2 * (T + 1) ≤ (T + 3) ^ 2 := by nlinarith
      calc 2 * q * (T + 1) = q * (2 * (T + 1)) := by ring
        _ ≤ q ^ 2 * (T + 3) ^ 2 := by gcongr
        _ = _ := by ring
    calc _ ≤ ((q * (T + 3)) ^ 2) ^ 2 := by gcongr
      _ = Real.exp (Real.log (q * (T + 3))) ^ 4 := by rw [Real.exp_log (by positivity)]; ring
      _ = Real.exp (4 * Real.log (q * (T + 3))) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have k4 : C3 * r * L ≤ K := by
    rw [mul_assoc]; exact le_trans (by gcongr; linarith) k1
  have k5 : K0 ≤ K := by
    have := le_abs_self K0
    have : E * 1 ≤ E * (r * L) := by gcongr
    linarith
  refine (H q T σ r L K hT (by linarith) r1 r3 r4 r2 (by linarith) k4 k5 k3 hN).trans ?_
  generalize r * L = x at *
  have e1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have e2 : x ≤ Real.exp x := by linarith
  calc _ ≤ D * Real.exp x * Real.exp (C * ((E + 1) * x)) * ((E + 1) * Real.exp x) ^ 2 := by
        gcongr
        exact k2.trans (by gcongr)
    _ = D * (E + 1) ^ 2 * Real.exp (B * x) := by
        rw [show B * x = x + C * ((E + 1) * x) + x + x by rw [hB]; ring]
        simp only [Real.exp_add]; ring
    _ ≤ D * (E + 1) ^ 2 * Real.exp (B * (2 + 6 * (1 - σ) * Real.log (q * T))) := by gcongr
    _ = _ := by
        rw [Real.rpow_def_of_pos (by positivity), mul_assoc _ (Real.exp _), ← Real.exp_add]
        congr 2; ring

end GlobalTheory.Lin.LogFree
