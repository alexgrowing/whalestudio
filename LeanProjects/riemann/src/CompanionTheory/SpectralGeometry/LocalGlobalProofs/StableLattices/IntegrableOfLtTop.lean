import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LineChainProof

def wt (R : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℝ := ‖u t‖ ^ 2 * Real.exp (2 * R * t)

def src (R : ℝ) (u g : ℝ → ℂ) (t : ℝ) : ℝ :=
  2 * Real.exp (2 * R * t) * (g t * (starRingEnd ℂ) (u t)).re

lemma wt_nonneg (R : ℝ) (u : ℝ → ℂ) (t : ℝ) : 0 ≤ wt R u t := by
  unfold wt; positivity

lemma wt_cont {u : ℝ → ℂ} (R : ℝ) (hu : Continuous u) : Continuous (wt R u) := by
  unfold wt; fun_prop

lemma src_cont {u g : ℝ → ℂ} (R : ℝ) (hu : Continuous u) (hg : Continuous g) :
    Continuous (src R u g) := by
  unfold src
  have : Continuous fun t => (g t * (starRingEnd ℂ) (u t)).re :=
    Complex.continuous_re.comp (hg.mul (Complex.continuous_conj.comp hu))
  exact (by fun_prop : Continuous fun t : ℝ => 2 * Real.exp (2 * R * t)).mul this

lemma hasDerivAt_wt {u g : ℝ → ℂ} {z : ℂ} {t : ℝ} (R : ℝ)
    (h : HasDerivAt u (z * u t + g t) t) :
    HasDerivAt (wt R u) (2 * (z.re + R) * wt R u t + src R u g t) t := by
  have h1 := h.norm_sq
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (2 * R * s)) (Real.exp (2 * R * t) * (2 * R)) t := by
    have : HasDerivAt (fun s : ℝ => 2 * R * s) (2 * R) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * R)
    exact this.exp
  have h3 := h1.mul h2
  have hin : inner ℝ (u t) (z * u t + g t) =
      z.re * ‖u t‖ ^ 2 + (g t * (starRingEnd ℂ) (u t)).re := by
    rw [Complex.inner]
    have e : (z * u t + g t) * (starRingEnd ℂ) (u t) =
        z * ((‖u t‖ ^ 2 : ℝ) : ℂ) + g t * (starRingEnd ℂ) (u t) := by
      have := Complex.conj_mul' (u t)
      push_cast
      rw [← this]; ring
    rw [e, Complex.add_re, Complex.re_mul_ofReal]
  refine HasDerivAt.congr_deriv (f := wt R u) h3 ?_
  rw [hin]; unfold wt src; ring

lemma abs_src_le (R : ℝ) (u g : ℝ → ℂ) (t : ℝ) {c : ℝ} (hc : 0 < c) :
    |src R u g t| ≤ c * wt R u t + wt R g t / c := by
  unfold src wt
  have hE : 0 < Real.exp (2 * R * t) := Real.exp_pos _
  generalize Real.exp (2 * R * t) = E at hE
  have h1 : |(g t * (starRingEnd ℂ) (u t)).re| ≤ ‖u t‖ * ‖g t‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    simp [mul_comm]
  have h2 : 2 * (‖u t‖ * ‖g t‖) ≤ c * ‖u t‖ ^ 2 + ‖g t‖ ^ 2 / c := by
    have h0 : 0 ≤ (c * ‖u t‖ - ‖g t‖) ^ 2 / c := by positivity
    have e : (c * ‖u t‖ - ‖g t‖) ^ 2 / c = c * ‖u t‖ ^ 2 + ‖g t‖ ^ 2 / c - 2 * (‖u t‖ * ‖g t‖) := by
      field_simp; ring
    linarith
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * E)]
  calc 2 * E * |(g t * (starRingEnd ℂ) (u t)).re| ≤ 2 * E * (‖u t‖ * ‖g t‖) := by gcongr
    _ = E * (2 * (‖u t‖ * ‖g t‖)) := by ring
    _ ≤ E * (c * ‖u t‖ ^ 2 + ‖g t‖ ^ 2 / c) := by gcongr
    _ = _ := by ring

section Energy

variable {u g : ℝ → ℂ} {z : ℂ} {R a : ℝ}

lemma energy (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t) {T : ℝ} (hT : 0 ≤ T) :
    wt R u T - wt R u 0 = ∫ t in (0 : ℝ)..T, (2 * (z.re + R) * wt R u t + src R u g t) := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_wt R (hd t ht.1)
  · exact ((continuous_const.mul (wt_cont R hu)).add (src_cont R hu hg)).intervalIntegrable _ _

lemma energy_le (hae : z.re + R = a) (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t) {T : ℝ} (hT : 0 ≤ T) {c : ℝ} (hc : 0 < c) :
    wt R u T - wt R u 0 ≤
      (2 * a + c) * (∫ t in (0 : ℝ)..T, wt R u t) + (∫ t in (0 : ℝ)..T, wt R g t) / c := by
  have cu := wt_cont R hu
  have cg := wt_cont R hg
  rw [energy hu hg hd hT, hae]
  have e : (2 * a + c) * (∫ t in (0 : ℝ)..T, wt R u t) + (∫ t in (0 : ℝ)..T, wt R g t) / c =
      ∫ t in (0 : ℝ)..T, ((2 * a + c) * wt R u t + wt R g t / c) := by
    have i1 : IntervalIntegrable (fun t => (2 * a + c) * wt R u t) volume 0 T :=
      (continuous_const.mul cu).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => wt R g t / c) volume 0 T :=
      (cg.div_const c).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div]
  rw [e]
  refine intervalIntegral.integral_mono_on hT
    (((continuous_const.mul cu).add (src_cont R hu hg)).intervalIntegrable _ _)
    (((continuous_const.mul cu).add (cg.div_const c)).intervalIntegrable _ _) fun t _ => ?_
  have h1 := abs_src_le R u g t hc
  have h2 := le_abs_self (src R u g t)
  have e2 : (2 * a + c) * wt R u t = 2 * a * wt R u t + c * wt R u t := by ring
  rw [e2]; linarith

lemma energy_ge (hae : z.re + R = a) (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t) {T : ℝ} (hT : 0 ≤ T) {c : ℝ} (hc : 0 < c) :
    (2 * a - c) * (∫ t in (0 : ℝ)..T, wt R u t) - (∫ t in (0 : ℝ)..T, wt R g t) / c ≤
      wt R u T - wt R u 0 := by
  have cu := wt_cont R hu
  have cg := wt_cont R hg
  rw [energy hu hg hd hT, hae]
  have e : (2 * a - c) * (∫ t in (0 : ℝ)..T, wt R u t) - (∫ t in (0 : ℝ)..T, wt R g t) / c =
      ∫ t in (0 : ℝ)..T, ((2 * a - c) * wt R u t - wt R g t / c) := by
    have i1 : IntervalIntegrable (fun t => (2 * a - c) * wt R u t) volume 0 T :=
      (continuous_const.mul cu).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => wt R g t / c) volume 0 T :=
      (cg.div_const c).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div]
  rw [e]
  refine intervalIntegral.integral_mono_on hT
    (((continuous_const.mul cu).sub (cg.div_const c)).intervalIntegrable _ _)
    (((continuous_const.mul cu).add (src_cont R hu hg)).intervalIntegrable _ _) fun t _ => ?_
  have h1 := abs_src_le R u g t hc
  have h2 := neg_abs_le (src R u g t)
  have e2 : (2 * a - c) * wt R u t = 2 * a * wt R u t - c * wt R u t := by ring
  rw [e2]; linarith

lemma iint_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (h0 : ∀ t, 0 ≤ f t) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, f t ≤ ∫ t in Ioi (0 : ℝ), f t := by
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_mono_set hf (ae_of_all _ h0) Ioc_subset_Ioi_self.eventuallyLE

lemma iint_mono {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ t, 0 ≤ f t) {S T : ℝ} (hS : 0 ≤ S)
    (hST : S ≤ T) : ∫ t in (0 : ℝ)..S, f t ≤ ∫ t in (0 : ℝ)..T, f t :=
  intervalIntegral.integral_mono_interval le_rfl hS hST (ae_of_all _ h0)
    (hf.intervalIntegrable _ _)

theorem step_pos (hae : z.re + R = a) (ha : 0 < a) (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t)
    (iu : IntegrableOn (wt R u) (Ioi 0)) {P : ℝ}
    (hP : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, wt R g t ≤ P) :
    a * ∫ t in Ioi (0 : ℝ), wt R u t ≤ P / a := by
  have cu := wt_cont R hu
  have base : ∀ T, 0 ≤ T → a * ∫ t in (0 : ℝ)..T, wt R u t ≤ wt R u T + P / a := by
    intro T hT
    have h1 := energy_ge hae hu hg hd hT ha
    have h3 := wt_nonneg R u 0
    have h4 : (∫ t in (0 : ℝ)..T, wt R g t) / a ≤ P / a := by
      have := hP T hT
      gcongr
    have e : 2 * a - a = a := by ring
    rw [e] at h1
    linarith
  have nth : ∀ n : ℕ, a * ∫ t in (0 : ℝ)..n, wt R u t ≤
      ((∫ t in (0 : ℝ)..((n : ℝ) + 1), wt R u t) - ∫ t in (0 : ℝ)..n, wt R u t) + P / a := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : ∫ _t in (n : ℝ)..((n : ℝ) + 1), (a * ∫ s in (0 : ℝ)..n, wt R u s) ≤
        ∫ t in (n : ℝ)..((n : ℝ) + 1), (wt R u t + P / a) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _)
        ((cu.add continuous_const).intervalIntegrable _ _) fun t ht => ?_
      have h2 := iint_mono cu (wt_nonneg R u) hn ht.1
      have h3 := base t (hn.trans ht.1)
      have h4 : a * ∫ s in (0 : ℝ)..n, wt R u s ≤ a * ∫ s in (0 : ℝ)..t, wt R u s := by gcongr
      linarith
    rw [intervalIntegral.integral_add (cu.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const] at h1
    have h2 : (∫ t in (0 : ℝ)..((n : ℝ) + 1), wt R u t) - ∫ t in (0 : ℝ)..n, wt R u t =
        ∫ t in (n : ℝ)..((n : ℝ) + 1), wt R u t :=
      intervalIntegral.integral_interval_sub_left (cu.intervalIntegrable _ _)
        (cu.intervalIntegrable _ _)
    rw [h2]
    simpa using h1
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 iu tendsto_natCast_atTop_atTop
  have t2 := intervalIntegral_tendsto_integral_Ioi (b := fun n : ℕ => (n : ℝ) + 1) 0 iu
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have := le_of_tendsto_of_tendsto' (t1.const_mul a) ((t2.sub t1).add_const (P / a)) nth
  simpa using this

theorem step_neg {b : ℝ} (hae : z.re + R = -b) (hb : 0 < b) (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t)
    (iu : IntegrableOn (wt R u) (Ioi 0)) {P : ℝ}
    (hP : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, wt R g t ≤ P) :
    b * ∫ t in Ioi (0 : ℝ), wt R u t ≤ wt R u 0 + P / b := by
  have base : ∀ n : ℕ, b * ∫ t in (0 : ℝ)..n, wt R u t ≤ wt R u 0 + P / b := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 := energy_le hae hu hg hd hn hb
    have h3 := wt_nonneg R u n
    have h4 : (∫ t in (0 : ℝ)..n, wt R g t) / b ≤ P / b := by
      have := hP n hn
      gcongr
    have e : 2 * -b + b = -b := by ring
    rw [e] at h1
    linarith
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 iu tendsto_natCast_atTop_atTop
  exact le_of_tendsto' (t1.const_mul b) base

theorem init_bound {b : ℝ} (hae : z.re + R = -b) (hb : 0 < b) (hu : Continuous u) (hg : Continuous g)
    (hd : ∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t) {P : ℝ}
    (hP : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, wt R g t ≤ P) :
    wt R u 0 ≤ (2 + 2 * b) * (∫ t in (0 : ℝ)..1, wt R u t) + P := by
  have cu := wt_cont R hu
  have key : ∀ t ∈ Icc (0 : ℝ) 1, wt R u 0 ≤
      wt R u t + ((1 + 2 * b) * (∫ s in (0 : ℝ)..1, wt R u s) + P) := by
    intro t ht
    have h1 := energy_ge hae hu hg hd ht.1 one_pos
    have h2 := iint_mono cu (wt_nonneg R u) ht.1 ht.2
    have h3 := hP t ht.1
    have h4 : (1 + 2 * b) * (∫ s in (0 : ℝ)..t, wt R u s) ≤
        (1 + 2 * b) * ∫ s in (0 : ℝ)..1, wt R u s := by gcongr
    rw [div_one] at h1
    linarith
  have h : ∫ _t in (0 : ℝ)..1, wt R u 0 ≤ ∫ t in (0 : ℝ)..1,
      (wt R u t + ((1 + 2 * b) * (∫ s in (0 : ℝ)..1, wt R u s) + P)) :=
    intervalIntegral.integral_mono_on zero_le_one (continuous_const.intervalIntegrable _ _)
      ((cu.add continuous_const).intervalIntegrable _ _) key
  rw [intervalIntegral.integral_add (cu.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_const] at h
  simp only [sub_zero, one_smul] at h
  linarith

lemma unit_le (hu : Continuous u) :
    ∫ t in (0 : ℝ)..1, wt R u t ≤ Real.exp (2 * |R|) * ∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  have i1 : IntegrableOn (wt R u) (Ioc 0 1) := (wt_cont R hu).integrableOn_Ioc
  have i2 : IntegrableOn (fun t => Real.exp (2 * |R|) * ‖u t‖ ^ 2) (Ioc 0 1) :=
    Continuous.integrableOn_Ioc (by fun_prop)
  refine setIntegral_mono_on i1 i2 measurableSet_Ioc fun t ht => ?_
  unfold wt
  rw [mul_comm]
  have : 2 * R * t ≤ 2 * |R| := by
    have h1 : R * t ≤ |R| * t := by
      have := le_abs_self R
      have := ht.1.le
      gcongr
    have h2 : |R| * t ≤ |R| * 1 := by
      have := ht.2
      gcongr
    linarith
  gcongr

end Energy

theorem step {z : ℂ} {R : ℝ} (ha : z.re + R ≠ 0) : ∃ K : ℝ, 0 < K ∧
    ∀ u g : ℝ → ℂ, Continuous u → Continuous g →
      (∀ t, 0 ≤ t → HasDerivAt u (z * u t + g t) t) →
      IntegrableOn (wt R u) (Ioi 0) → IntegrableOn (wt R g) (Ioi 0) →
      ∫ t in Ioi (0 : ℝ), wt R u t ≤
        K * ((∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2) + ∫ t in Ioi (0 : ℝ), wt R g t) := by
  rcases lt_or_gt_of_ne ha with h | h
  · obtain ⟨b, hae⟩ : ∃ b, z.re + R = -b := ⟨-(z.re + R), by ring⟩
    have hb : 0 < b := by linarith
    have hE : 0 < Real.exp (2 * |R|) := Real.exp_pos _
    refine ⟨((2 + 2 * b) * Real.exp (2 * |R|) + (1 + 1 / b)) / b, by positivity, ?_⟩
    intro u g hu hg hd iu ig
    have hP := fun T hT => iint_le ig (wt_nonneg R g) (T := T) hT
    have h1 := step_neg hae hb hu hg hd iu hP
    have h2 := init_bound hae hb hu hg hd hP
    have h3 := unit_le (R := R) hu
    have hX : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2 := integral_nonneg fun t => by positivity
    have hW : 0 ≤ ∫ t in Ioi (0 : ℝ), wt R g t := integral_nonneg (wt_nonneg R g)
    generalize (∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2) = X at *
    generalize (∫ t in Ioi (0 : ℝ), wt R g t) = P at *
    generalize (∫ t in Ioi (0 : ℝ), wt R u t) = W at *
    generalize Real.exp (2 * |R|) = E at *
    have h4 : (2 + 2 * b) * (∫ t in (0 : ℝ)..1, wt R u t) ≤ (2 + 2 * b) * (E * X) := by gcongr
    have hD : 0 ≤ (2 + 2 * b) * E := by positivity
    have hQ : 0 ≤ 1 + 1 / b := by positivity
    have e : b * (((2 + 2 * b) * E + (1 + 1 / b)) / b * (X + P)) =
        ((2 + 2 * b) * E + (1 + 1 / b)) * (X + P) := by
      field_simp
    have e2 : P / b = 1 / b * P := by ring
    refine le_of_mul_le_mul_left ?_ hb
    rw [e]
    nlinarith [mul_nonneg hD hW, mul_nonneg hQ hX]
  · obtain ⟨a, hae⟩ : ∃ a, z.re + R = a := ⟨_, rfl⟩
    have ha' : 0 < a := by linarith
    refine ⟨1 / (a * a), by positivity, ?_⟩
    intro u g hu hg hd iu ig
    have hP := fun T hT => iint_le ig (wt_nonneg R g) (T := T) hT
    have h1 := step_pos hae ha' hu hg hd iu hP
    have hX : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2 := integral_nonneg fun t => by positivity
    generalize (∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2) = X at *
    generalize (∫ t in Ioi (0 : ℝ), wt R g t) = P at *
    generalize (∫ t in Ioi (0 : ℝ), wt R u t) = W at *
    have e : a * (1 / (a * a) * (X + P)) = X / a + P / a := by
      field_simp
    refine le_of_mul_le_mul_left ?_ ha'
    rw [e]
    have : 0 ≤ X / a := by positivity
    linarith

theorem chain (m : ℕ) (z : Fin m → ℂ) (R : ℝ) (hz : ∀ k, (z k).re + R ≠ 0) : ∃ C : ℝ, 0 < C ∧
    ∀ F : Fin (m + 1) → ℝ → ℂ,
      (∀ (k : Fin m) (t : ℝ), 0 ≤ t →
        HasDerivAt (F k.succ) (z k * F k.succ t + F k.castSucc t) t) →
      (∀ k, Continuous (F k)) →
      (∀ k, IntegrableOn (wt R (F k)) (Ioi 0)) →
      ∫ t in Ioi (0 : ℝ), wt R (F (Fin.last m)) t ≤
        C * ((∑ k, ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2) + ∫ t in Ioi (0 : ℝ), wt R (F 0) t) := by
  induction m with
  | zero =>
    refine ⟨1, one_pos, fun F _ _ _ => ?_⟩
    have hX : 0 ≤ ∑ k, ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun t => by positivity
    have e : Fin.last 0 = (0 : Fin 1) := rfl
    rw [e]
    linarith
  | succ m ih =>
    obtain ⟨C, hC, H⟩ := ih (fun k => z k.castSucc) (fun k => hz k.castSucc)
    obtain ⟨K, hK, S⟩ := step (hz (Fin.last m))
    refine ⟨K * (1 + C), by positivity, fun F hd hc hi => ?_⟩
    have h1 := H (fun k => F k.castSucc)
      (fun k t ht => by
        have := hd k.castSucc t ht
        rw [Fin.succ_castSucc] at this
        exact this)
      (fun k => hc _) (fun k => hi _)
    have h2 := S (F (Fin.last (m + 1))) (F (Fin.last m).castSucc) (hc _) (hc _)
      (fun t ht => by
        have := hd (Fin.last m) t ht
        rw [Fin.succ_last] at this
        exact this)
      (hi _) (hi _)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero] at h1
    have hS : 0 ≤ ∑ k : Fin (m + 1), ∫ t in Ioc (0 : ℝ) 1, ‖F k.castSucc t‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun t => by positivity
    have hX : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖F (Fin.last (m + 1)) t‖ ^ 2 :=
      integral_nonneg fun t => by positivity
    have hW : 0 ≤ ∫ t in Ioi (0 : ℝ), wt R (F 0) t := integral_nonneg (wt_nonneg R _)
    generalize (∑ k : Fin (m + 1), ∫ t in Ioc (0 : ℝ) 1, ‖F k.castSucc t‖ ^ 2) = A at *
    generalize (∫ t in Ioc (0 : ℝ) 1, ‖F (Fin.last (m + 1)) t‖ ^ 2) = X at *
    generalize (∫ t in Ioi (0 : ℝ), wt R (F 0) t) = W0 at *
    generalize (∫ t in Ioi (0 : ℝ), wt R (F (Fin.last m).castSucc) t) = Wm at *
    refine h2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    nlinarith [mul_nonneg hC.le hX]

lemma enn_wt (S : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * S * t)) = ENNReal.ofReal (wt S u t) := by
  unfold wt
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma integrable_of_lt_top {S : ℝ} {u : ℝ → ℂ} (hu : Continuous u)
    (h : ∫⁻ t in Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * S * t)) < ⊤) :
    IntegrableOn (wt S u) (Ioi 0) := by
  simp_rw [enn_wt] at h
  refine ⟨(wt_cont S hu).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (wt_nonneg S u))]
  exact h

lemma lint_wt {S : ℝ} {u : ℝ → ℂ} (hi : IntegrableOn (wt S u) (Ioi 0)) :
    ∫⁻ t in Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * S * t)) =
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), wt S u t) := by
  simp_rw [enn_wt]
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (wt_nonneg S u))).symm

lemma lint_unit {u : ℝ → ℂ} (hu : Continuous u) :
    ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖u t‖ ^ 2) = ∫⁻ t in Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 := by
  have i : IntegrableOn (fun t => ‖u t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    Continuous.integrableOn_Ioc (by fun_prop)
  rw [ofReal_integral_eq_lintegral_ofReal i (ae_of_all _ fun t => by positivity)]
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lineChain : CompanionTheory.RgExh.Dec.L.LineChain := by
  intro m z R R' hRR hz
  obtain ⟨C, hC, H⟩ := chain m z R (fun k h => hz k (by linarith))
  refine ⟨C, hC, fun F hd hc hfin => ?_⟩
  have hint : ∀ k, IntegrableOn (wt R (F k)) (Ioi 0) := by
    intro k
    refine Integrable.mono' (integrable_of_lt_top (hc k) (hfin k))
      (wt_cont R (hc k)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
    rw [Real.norm_of_nonneg (wt_nonneg R _ t)]
    unfold wt
    have : 2 * R * t ≤ 2 * R' * t := by
      have := mem_Ioi.1 ht
      gcongr
    gcongr
  have key := H F hd hc hint
  rw [lint_wt (hint (Fin.last m)), lint_wt (hint 0)]
  have hX : ∀ k, 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2 :=
    fun k => integral_nonneg fun t => by positivity
  have hW : 0 ≤ ∫ t in Ioi (0 : ℝ), wt R (F 0) t := integral_nonneg (wt_nonneg R _)
  generalize hI : ENNReal.ofReal (∫ t in Ioi (0 : ℝ), wt R (F 0) t) = I
  have e : ∀ k, ∫⁻ t in Ioc (0 : ℝ) 1, (‖F k t‖ₑ ^ 2 + I) =
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2) + I := by
    intro k
    rw [lintegral_add_right _ measurable_const, lintegral_const, ← lint_unit (hc k)]
    simp
  simp_rw [e]
  calc ENNReal.ofReal (∫ t in Ioi (0 : ℝ), wt R (F (Fin.last m)) t)
      ≤ ENNReal.ofReal (C * ((∑ k, ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2) +
          ∫ t in Ioi (0 : ℝ), wt R (F 0) t)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal C * ((∑ k, ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2)) + I) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hX k) hW,
          ENNReal.ofReal_sum_of_nonneg fun k _ => hX k, hI]
    _ ≤ ENNReal.ofReal C * ∑ k, (ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ ^ 2) + I) := by
        rw [Finset.sum_add_distrib]
        gcongr
        exact Finset.single_le_sum (f := fun _ : Fin (m + 1) => I) (fun _ _ => zero_le)
          (Finset.mem_univ 0)

end GlobalTheory.CompanionTheory.LineChainProof
