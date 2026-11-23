import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LogDeriv

open LSeries
open scoped LSeries.notation

lemma absc_lt {a : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv a < s.re := by
  have h : abscissaOfAbsConv a ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      ha (y : ℂ) (by simpa using hy)
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hs)

lemma hasDerivAt_of_conv {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries a) (-(LSeries l s * LSeries a s)) s := by
  have h := LSeries_hasDerivAt (absc_lt ha hs)
  have hlog : LSeries (logMul a) s = LSeries (l ⍟ a) s := LSeries_congr (fun {n} hn => hc n hn) s
  rwa [hlog, LSeries_convolution' (hl s hs) (ha s hs)] at h

lemma logMul_div {l : ℕ → ℂ} (h1 : l 1 = 0) {n : ℕ} (hn : n ≠ 0) :
    logMul (fun n => l n / Complex.log n) n = l n := by
  show Complex.log (n : ℂ) * (l n / Complex.log (n : ℂ)) = l n
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [h1]
  · have hn2 : 1 < n := by omega
    have hlog : Complex.log (n : ℂ) ≠ 0 := by
      rw [← Complex.natCast_log]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn2)).ne'
    field_simp

private lemma norm_div_log_natCast_le_norm_div_log_two (x : ℂ) (n : ℕ) : ‖x / Complex.log n‖ ≤ ‖x‖ / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : Complex.log (n : ℂ) = 0 := by
      interval_cases n <;> simp
    rw [h0, div_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) hl2.le
  · have hge : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [← Complex.natCast_log, norm_div, Complex.norm_of_nonneg (hl2.le.trans hge)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hl2 hge

private lemma LSeriesSummable_div_log_of_LSeriesSummable {l : ℕ → ℂ} (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => l n / Complex.log n) s := by
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term l s n‖ / Real.log 2)
    ((summable_norm_iff.mpr (hl s hs)).div_const _) (fun n => ?_)
  simp only [LSeries.norm_term_eq]
  split_ifs
  · simp
  · rw [div_right_comm]
    gcongr
    exact norm_div_log_natCast_le_norm_div_log_two _ _

lemma absc_div_lt {l : ℕ → ℂ} (h1 : l 1 = 0) (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    {s : ℂ} (hs : 1 < s.re) : abscissaOfAbsConv (fun n => l n / Complex.log n) < s.re := by
  have h : abscissaOfAbsConv (fun n => l n / Complex.log n) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_div_log_of_LSeriesSummable hl (by simpa using hy)
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hs)

lemma eq_exp_of_conv {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s) (a1 : a 1 = 1) (l1 : l 1 = 0)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    LSeries a s = exp (LSeries (fun n => l n / Complex.log n) s) := by
  have hUo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : ∀ z : ℂ, 1 < z.re →
      HasDerivAt (LSeries (fun n => l n / Complex.log n)) (-LSeries l z) z := by
    intro z hz
    have h := LSeries_hasDerivAt (absc_div_lt l1 hl hz)
    rwa [LSeries_congr (fun {n} hn => logMul_div l1 hn) z] at h
  have hH : ∀ z : ℂ, 1 < z.re → HasDerivAt
      (fun w => LSeries a w * Complex.exp (-LSeries (fun n => l n / Complex.log n) w)) 0 z := by
    intro z hz
    have h : HasDerivAt
        (fun w => LSeries a w * Complex.exp (-LSeries (fun n => l n / Complex.log n) w))
        (-(LSeries l z * LSeries a z) * Complex.exp (-LSeries (fun n => l n / Complex.log n) z) +
          LSeries a z * (Complex.exp (-LSeries (fun n => l n / Complex.log n) z) *
            -(-LSeries l z))) z :=
      (hasDerivAt_of_conv ha hl hc hz).mul (hG z hz).neg.cexp
    exact h.congr_deriv (by ring)
  have hconst : ∀ z : ℂ, 1 < z.re →
      LSeries a z * Complex.exp (-LSeries (fun n => l n / Complex.log n) z) =
        LSeries a s * Complex.exp (-LSeries (fun n => l n / Complex.log n) s) := fun z hz =>
    hUo.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 1).isPreconnected
      (fun v hv => (hH v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hH v hv).deriv) hz hs
  have hab : abscissaOfAbsConv a < ⊤ := (absc_lt ha hs).trans (EReal.coe_lt_top _)
  have hlb : abscissaOfAbsConv (fun n => l n / Complex.log n) < ⊤ :=
    (absc_div_lt l1 hl hs).trans (EReal.coe_lt_top _)
  have hlim : Tendsto
      (fun x : ℝ => LSeries a x * Complex.exp (-LSeries (fun n => l n / Complex.log n) x)) atTop
      (𝓝 (a 1 * Complex.exp (-((fun n => l n / Complex.log n) 1)))) :=
    (LSeries.tendsto_atTop hab).mul
      ((Complex.continuous_exp.tendsto _).comp (LSeries.tendsto_atTop hlb).neg)
  have hev : (fun x : ℝ => LSeries a x * Complex.exp (-LSeries (fun n => l n / Complex.log n) x))
      =ᶠ[atTop] fun _ => LSeries a s * Complex.exp (-LSeries (fun n => l n / Complex.log n) s) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hconst x (by simpa using hx)
  have hval := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  simp only [a1, l1, zero_div, neg_zero, Complex.exp_zero, mul_one] at hval
  have h2 := hval.symm
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2

lemma summable_of_le {l : ℕ → ℂ} (hl : ∀ n, ‖l n‖ ≤ 2 * Λ n) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable l s := by
  have hΛ := LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm_bounded (g := fun n => 2 * ‖LSeries.term (↗Λ) s n‖)
    ((summable_norm_iff.mpr hΛ).mul_left 2) (fun n => ?_)
  simp only [LSeries.norm_term_eq]
  split_ifs
  · simp
  · rw [← mul_div_assoc]
    gcongr
    rw [Complex.norm_of_nonneg vonMangoldt_nonneg]
    exact hl n

lemma norm_ge_of_conv {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ n, ‖l n‖ ≤ 2 * Λ n) (a1 : a 1 = 1)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries a s‖ := by
  have l1 : l 1 = 0 := by simpa using hl 1
  have hl' : ∀ z : ℂ, 1 < z.re → LSeriesSummable l z := fun z hz => summable_of_le hl z hz
  have hΛs : ∀ z : ℂ, 1 < z.re → LSeriesSummable (↗Λ) z := fun z hz =>
    LSeriesSummable_vonMangoldt hz
  have h1s : ∀ z : ℂ, 1 < z.re → LSeriesSummable (1 : ℕ → ℂ) z := fun z hz =>
    LSeriesSummable_one_iff.mpr hz
  have hΛ1 : (↗Λ) 1 = 0 := by simp
  have hcz : ∀ n : ℕ, n ≠ 0 → Complex.log n * (1 : ℕ → ℂ) n = ((↗Λ) ⍟ (1 : ℕ → ℂ)) n := by
    intro n _
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun x _ => ((Λ x : ℝ) : ℂ)), ← Complex.ofReal_sum,
      vonMangoldt_sum, Complex.natCast_log]
  have hσc : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hζ := eq_exp_of_conv h1s hΛs (by simp) hΛ1 hcz hσc
  have hA := eq_exp_of_conv ha hl' a1 l1 hc hs

  set t : ℕ → ℂ := fun n => LSeries.term (fun n => (↗Λ) n / Complex.log n) ((s.re : ℝ) : ℂ) n
    with ht
  have htn : ∀ n, t n = ((‖t n‖ : ℝ) : ℂ) := by
    intro n
    open ComplexOrder in
    (refine Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg ?_ s.re)
     show (0 : ℂ) ≤ ((Λ n : ℝ) : ℂ) / Complex.log n
     rw [← Complex.natCast_log, ← Complex.ofReal_div]
     exact Complex.zero_le_real.mpr (div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)))
  have hts : Summable fun n => ‖t n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_of_abscissaOfAbsConv_lt_re (absc_div_lt hΛ1 hΛs hσc))
  set R : ℝ := ∑' n, ‖t n‖ with hR
  have hZ : LSeries (fun n => (↗Λ) n / Complex.log n) ((s.re : ℝ) : ℂ) = (R : ℂ) := by
    show ∑' n, t n = _
    rw [tsum_congr htn, ← Complex.ofReal_tsum]
  have hζb : Real.exp R ≤ s.re / (s.re - 1) := by
    have hb := GlobalTheory.LLower.norm_LSeries_le (f := (1 : ℕ → ℂ)) (fun n => by simp) hσc
    rw [hζ, hZ, Complex.norm_exp, Complex.ofReal_re] at hb
    simpa using hb

  have hgs : Summable fun n => ‖LSeries.term (fun n => l n / Complex.log n) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_of_abscissaOfAbsConv_lt_re (absc_div_lt l1 hl' hs))
  have hpt : ∀ n, ‖LSeries.term (fun n => l n / Complex.log n) s n‖ ≤ 2 * ‖t n‖ := by
    intro n
    simp only [ht, LSeries.norm_term_eq, Complex.ofReal_re]
    split_ifs
    · simp
    · rw [norm_div, norm_div, Complex.norm_of_nonneg vonMangoldt_nonneg, ← mul_div_assoc,
        ← mul_div_assoc]
      gcongr
      exact hl n
  have hGle : ‖LSeries (fun n => l n / Complex.log n) s‖ ≤ 2 * R := by
    calc ‖LSeries (fun n => l n / Complex.log n) s‖
        ≤ ∑' n, ‖LSeries.term (fun n => l n / Complex.log n) s n‖ := norm_tsum_le_tsum_norm hgs
      _ ≤ ∑' n, 2 * ‖t n‖ := hgs.tsum_le_tsum hpt (hts.mul_left 2)
      _ = 2 * R := hts.tsum_mul_left 2
  have hre : -(2 * R) ≤ (LSeries (fun n => l n / Complex.log n) s).re := by
    have := Complex.abs_re_le_norm (LSeries (fun n => l n / Complex.log n) s)
    have := neg_abs_le (LSeries (fun n => l n / Complex.log n) s).re
    linarith
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < s.re - 1 := by linarith
  have hR1 : (s.re - 1) / s.re ≤ Real.exp (-R) := by
    rw [Real.exp_neg, ← inv_div]
    exact inv_anti₀ (Real.exp_pos R) hζb
  calc ((s.re - 1) / s.re) ^ 2 ≤ Real.exp (-R) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hs1.le hs0.le) hR1 2
    _ = Real.exp (-(2 * R)) := by rw [sq, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (LSeries (fun n => l n / Complex.log n) s).re := Real.exp_le_exp.mpr hre
    _ = ‖LSeries a s‖ := by rw [hA, Complex.norm_exp]

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

lemma norm_lamChi_le (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  show ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ 2 * Λ n
  calc ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ ∑ g, ‖χ g * (𝓕.lam g n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ g, 𝓕.lam g n := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_of_nonneg (𝓕.lam_nonneg g n)]
    _ ≤ 2 * Λ n := 𝓕.lam_le n

lemma aChi_one : 𝓕.aChi χ 1 = 1 := by
  show ∑ g, χ g * (𝓕.a g 1 : ℂ) = 1
  rw [Finset.sum_eq_single (0 : 𝓕.G)]
  · rw [AddChar.map_zero_eq_one, 𝓕.a_one]
    simp
  · intro g _ hg
    rw [𝓕.a_one_ne g hg]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma conv_chi (n : ℕ) : Complex.log n * 𝓕.aChi χ n = (𝓕.lamChi χ ⍟ 𝓕.aChi χ) n := by
  rw [LSeries.convolution_def]
  show Complex.log (n : ℂ) * ∑ g, χ g * (𝓕.a g n : ℂ) =
    ∑ p ∈ n.divisorsAntidiagonal, (∑ h, χ h * (𝓕.lam h p.1 : ℂ)) * ∑ g, χ g * (𝓕.a g p.2 : ℂ)
  have step : ∀ g, Complex.log (n : ℂ) * (χ g * (𝓕.a g n : ℂ)) =
      ∑ h, ∑ p ∈ n.divisorsAntidiagonal, χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := by
    intro g
    have hc := congrArg (fun r : ℝ => (r : ℂ)) (𝓕.conv g n)
    simp only [Complex.ofReal_mul, Complex.ofReal_sum] at hc
    simp_rw [← Finset.mul_sum]
    rw [← hc, ← Complex.natCast_log]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun g _ => step g)]
  calc ∑ g, ∑ h, ∑ p ∈ n.divisorsAntidiagonal,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ))
      = ∑ h, ∑ g, ∑ p ∈ n.divisorsAntidiagonal,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := Finset.sum_comm
    _ = ∑ h, ∑ p ∈ n.divisorsAntidiagonal, ∑ g,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ h, ∑ g,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := Finset.sum_comm
    _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ h, ∑ g,
        χ h * (𝓕.lam h p.1 : ℂ) * (χ g * (𝓕.a g p.2 : ℂ)) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun h _ => ?_
        refine Fintype.sum_equiv (Equiv.subRight h) _ _ fun g => ?_
        have hχ : χ g = χ h * χ (g - h) := by
          rw [← AddChar.map_add_eq_mul]
          congr 1
          abel
        simp only [Equiv.subRight_apply]
        rw [hχ]
        ring
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (∑ h, χ h * (𝓕.lam h p.1 : ℂ)) * ∑ g, χ g * (𝓕.a g p.2 : ℂ) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]

theorem logDeriv_F : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by
  intro 𝓕 χ s hs
  obtain ⟨-, hLS, -, -⟩ := GlobalTheory.Hk.RayCont.continuation_growth 𝓕 χ
  have ha : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.aChi χ) z := fun z hz => (hLS z hz).1
  have hl : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.lamChi χ) z := fun z hz =>
    summable_of_le (norm_lamChi_le 𝓕 χ) z hz
  have hlb := norm_ge_of_conv ha (norm_lamChi_le 𝓕 χ) (aChi_one 𝓕 χ)
    (fun n _ => conv_chi 𝓕 χ n) hs
  have hσ : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL0 : LSeries (𝓕.aChi χ) s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlb
    linarith [pow_pos hσ 2]
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hder := hasDerivAt_of_conv ha hl (fun n _ => conv_chi 𝓕 χ n) hs
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨hl s hs, hlb, ?_, ?_⟩
  · rw [(hLS s hs).2]
    split_ifs <;> simp [hs1, hL0]
  · by_cases h : χ = 1
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] fun z => (z - 1) * LSeries (𝓕.aChi χ) z :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_pos h]
      have hd : HasDerivAt (fun z => (z - 1) * LSeries (𝓕.aChi χ) z)
          (1 * LSeries (𝓕.aChi χ) s +
            (s - 1) * (-(LSeries (𝓕.lamChi χ) s * LSeries (𝓕.aChi χ) s))) s :=
        ((hasDerivAt_id s).sub_const (1 : ℂ)).mul hder
      rw [hev.deriv_eq, hd.deriv, (hLS s hs).2, if_pos h, if_pos h]
      field_simp
      ring
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] LSeries (𝓕.aChi χ) :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_neg h, one_mul]
      rw [hev.deriv_eq, hder.deriv, (hLS s hs).2, if_neg h, if_neg h, one_mul]
      field_simp
      ring

end GlobalTheory.Hk.LogDeriv
