import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Density

theorem integral_norm_sq (f : ℝ → ℝ) :
    ∫ z : ℂ, f (‖z‖ ^ 2) = Real.pi * ∫ r in Set.Ioi (0 : ℝ), f r := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) (fun r => f (r ^ 2)),
    ← integral_comp_rpow_Ioi f (p := 2) two_ne_zero]
  have : ∫ x in Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • f (x ^ (2 : ℝ)) =
      2 * ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f (y ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    norm_num [mul_assoc]
  rw [this]
  simp [Measure.real, Complex.volume_ball]
  ring

def expAvg (G : ℝ → ℝ) (σ t : ℝ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), Real.exp (-r) * G (t - σ * r)

theorem hasDerivAt_expAvg_one {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) {t : ℝ}
    (hc : ContinuousAt G t) : HasDerivAt (expAvg G 1) (G t - expAvg G 1 t) t := by
  have hint : ∀ s : ℝ, IntegrableOn (fun u => Real.exp u * G u) (Set.Iic s) := fun s =>
    (integrableOn_exp_Iic s).mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hE : ∀ s : ℝ, expAvg G 1 s = Real.exp (-s) * ∫ u in Set.Iic s, Real.exp u * G u := by
    intro s
    have h1 := integral_comp_neg_Iic s (fun x => Real.exp (-x) * G (-x))
    have h2 := integral_sub_right_eq_self
      ((Set.Ioi (-s)).indicator fun x => Real.exp (-x) * G (-x)) s (μ := volume)
    simp only [neg_neg] at h1
    rw [h1, ← integral_indicator measurableSet_Ioi, ← h2, ← integral_const_mul, expAvg,
      ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : x - s ∈ Set.Ioi (-s) ↔ x ∈ Set.Ioi 0 := by
      simp only [Set.mem_Ioi]; constructor <;> intro h <;> linarith
    simp only [Set.indicator, this]
    split_ifs
    · rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    · simp
  have hI : HasDerivAt (fun s => ∫ u in Set.Iic s, Real.exp u * G u) (Real.exp t * G t) t := by
    have h1 : (fun s => ∫ u in Set.Iic s, Real.exp u * G u) =
        fun s => (∫ u in Set.Iic t, Real.exp u * G u) + ∫ u in t..s, Real.exp u * G u := by
      funext s
      rw [← intervalIntegral.integral_Iic_sub_Iic (hint t) (hint s)]; ring
    rw [h1]
    refine HasDerivAt.const_add _ (intervalIntegral.integral_hasDerivAt_right (by simp) ?_ ?_)
    · exact (Real.measurable_exp.mul hm).stronglyMeasurable.stronglyMeasurableAtFilter
    · exact Real.continuous_exp.continuousAt.mul hc
  have h := ((hasDerivAt_id t).neg.exp).mul hI
  rw [funext hE]
  refine HasDerivAt.congr_deriv h ?_
  simp only [Pi.neg_apply, id]
  rw [← mul_assoc, ← Real.exp_add]; simp; ring

theorem hasDerivAt_expAvg {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool) {t : ℝ}
    (hc : ContinuousAt G t) :
    HasDerivAt (expAvg G (sgn ℝ s)) (sgn ℝ s * (G t - expAvg G (sgn ℝ s) t)) t := by
  cases s
  · have h1 : ∀ u, expAvg G (-1) u = expAvg (fun x => G (-x)) 1 (-u) := by
      intro u; unfold expAvg; congr 1; funext r; congr 2; ring
    have hc' : ContinuousAt (fun x => G (-x)) (-t) :=
      ContinuousAt.comp (f := fun x : ℝ => -x) (by simpa using hc) continuous_neg.continuousAt
    have h := (hasDerivAt_expAvg_one (G := fun x => G (-x)) (hm.comp measurable_neg) (fun u => hb _) hc').comp t
      (hasDerivAt_neg t)
    have hs : sgn ℝ false = -1 := by simp [sgn]
    rw [hs, funext h1]
    refine HasDerivAt.congr_deriv h ?_
    simp
  · have hs : sgn ℝ true = 1 := by simp [sgn]
    rw [hs, one_mul]
    exact hasDerivAt_expAvg_one hm hb hc

theorem expAvg_pos {G : ℝ → ℝ} (hm : Monotone G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool)
    (h : G (-1) < G 1) : 0 < sgn ℝ s * (G (sgn ℝ s) - expAvg G (sgn ℝ s) (sgn ℝ s)) := by
  set σ := sgn ℝ s with hσ
  have he : IntegrableOn (fun r => Real.exp (-r)) (Set.Ioi (0 : ℝ)) := integrableOn_exp_neg_Ioi 0
  have h1 : IntegrableOn (fun r => Real.exp (-r) * G (σ - σ * r)) (Set.Ioi (0 : ℝ)) :=
    he.mul_bdd (hm.measurable.comp (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun _ => hb _)
  have h2 : σ * (G σ - expAvg G σ σ) =
      ∫ r in Set.Ioi (0 : ℝ), σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) := by
    rw [integral_const_mul, integral_sub (he.mul_const _) h1, integral_mul_const, integral_exp_neg_Ioi_zero,
      one_mul, expAvg]
  have hle : ∀ r, 0 ≤ r → 0 ≤ σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (-1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ 1 by linarith)
      linarith
  have hlt : ∀ r, 2 < r → 0 < σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ -1 by linarith)
      linarith
  have e : ∀ r, σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) =
      Real.exp (-r) * (σ * (G σ - G (σ - σ * r))) := fun r => by ring
  rw [h2, setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le (show 0 < volume (Set.Ioi (2 : ℝ)) by simp) (measure_mono fun r hr => ⟨?_, ?_⟩)
    · rw [Function.mem_support, e]
      exact (mul_pos (Real.exp_pos _) (hlt r hr)).ne'
    · exact (lt_trans two_pos (show (2 : ℝ) < r from hr) : (0 : ℝ) < r)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [e]
    exact mul_nonneg (Real.exp_pos _).le (hle r (le_of_lt hr))
  · exact ((he.mul_const _).sub h1).const_mul _

def cdf {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : ℝ := ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y

theorem continuous_qEps {n : ℕ} (ε : Fin n → Bool) : Continuous (qEps ε) := by
  unfold qEps; fun_prop

theorem measurableSet_qEps {n : ℕ} (ε : Fin n → Bool) (t : ℝ) :
    MeasurableSet {y : Fin n → ℂ | qEps ε y ≤ t} :=
  measurableSet_le (continuous_qEps ε).measurable measurable_const

theorem integrable_gauss (n : ℕ) : Integrable (gauss : (Fin n → ℂ) → ℝ) := by
  have h1 : Integrable fun z : ℂ => Real.exp (-‖z‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin n) (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) fun _ => h1
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [gauss, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem cdf_mono {n : ℕ} (ε : Fin n → Bool) : Monotone (cdf ε) := fun _ _ h =>
  setIntegral_mono_set (integrable_gauss n).integrableOn
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
    (HasSubset.Subset.eventuallyLE fun _ hy => le_trans hy h)

theorem abs_cdf_le {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : |cdf ε t| ≤ ∫ y : Fin n → ℂ, gauss y := by
  rw [abs_of_nonneg (show 0 ≤ cdf ε t from integral_nonneg fun y => (gauss_pos y).le)]
  exact setIntegral_le_integral (integrable_gauss n) (Filter.Eventually.of_forall fun y => (gauss_pos y).le)

theorem cdf_lt {n : ℕ} (ε : Fin n → Bool) : cdf ε (-1) < cdf ε 1 := by
  have h := integral_diff (measurableSet_qEps ε (-1))
    ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ 1}))
    (fun y (hy : qEps ε y ≤ -1) => show qEps ε y ≤ 1 by linarith)
  rw [← sub_pos, cdf, cdf, ← h, setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le) (integrable_gauss n).integrableOn]
  have ho : IsOpen (qEps ε ⁻¹' Set.Ioo (-1) 1) := isOpen_Ioo.preimage (continuous_qEps ε)
  refine lt_of_lt_of_le (ho.measure_pos volume ⟨0, by simp [qEps]⟩) (measure_mono fun y hy => ⟨?_, ?_, ?_⟩)
  · exact (gauss_pos y).ne'
  · exact hy.2.le
  · exact not_le.2 hy.1

theorem cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) (t : ℝ) :
    cdf ε t = Real.pi * expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) a).symm
  have hi := (integrable_gauss (n + 1)).indicator (measurableSet_qEps ε t)
  have hi' := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [cdf, ← integral_indicator (measurableSet_qEps ε t), ← hp.integral_comp', expAvg,
    ← integral_norm_sq fun r => Real.exp (-r) * cdf (fun i => ε (a.succAbove i)) (t - sgn ℝ (ε a) * r)]
  refine (integral_prod _ hi').trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [cdf]
  rw [← integral_indicator (measurableSet_qEps _ _), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp, Set.indicator, Set.mem_setOf_eq, qEps, gauss, Fin.sum_univ_succAbove _ a,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, sgn, le_sub_iff_add_le']
  split_ifs <;> simp [Real.exp_add, mul_comm]

theorem hasDerivAt_cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) {t : ℝ}
    (hc : ContinuousAt (cdf fun i => ε (a.succAbove i)) t) :
    HasDerivAt (cdf ε) (Real.pi * (sgn ℝ (ε a) * (cdf (fun i => ε (a.succAbove i)) t -
      expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t))) t := by
  rw [funext (cdf_succ ε a)]
  exact (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε a) hc).const_mul _

theorem cdf_zero_eventually (ε : Fin 0 → Bool) {t : ℝ} (ht : t ≠ 0) : cdf ε =ᶠ[nhds t] fun _ => cdf ε t := by
  rcases ht.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with u (hu : u < 0)
    simp [cdf, qEps, not_le.2 h, not_le.2 hu]
  · filter_upwards [Ioi_mem_nhds h] with u (hu : 0 < u)
    simp [cdf, qEps, h.le, hu.le]

theorem differentiableAt_cdf : ∀ {n : ℕ} (ε : Fin n → Bool) {t : ℝ}, t ≠ 0 → DifferentiableAt ℝ (cdf ε) t
  | 0, ε, _, ht => (differentiableAt_const _).congr_of_eventuallyEq (cdf_zero_eventually ε ht)
  | _ + 1, ε, _, ht => (hasDerivAt_cdf_succ ε 0 (differentiableAt_cdf _ ht).continuousAt).differentiableAt

theorem continuousOn_gaussDens : ∀ {n : ℕ} (ε : Fin n → Bool), ContinuousOn (gaussDens ε) {β | β ≠ 0}
  | 0, ε => (continuousOn_const (c := (0 : ℝ))).congr fun t ht => by
      show deriv (cdf ε) t = 0
      rw [(cdf_zero_eventually ε ht).deriv_eq]; simp
  | n + 1, ε => by
      have hc : ∀ t : ℝ, t ≠ 0 → ContinuousAt (cdf fun i => ε ((0 : Fin (n + 1)).succAbove i)) t :=
        fun t ht => (differentiableAt_cdf _ ht).continuousAt
      refine ContinuousOn.congr ?_ fun t ht => (hasDerivAt_cdf_succ ε 0 (hc t ht)).deriv
      refine fun t ht => ContinuousAt.continuousWithinAt ?_
      exact continuousAt_const.mul (continuousAt_const.mul ((hc t ht).sub
        (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε 0) (hc t ht)).continuousAt))

theorem gaussDens_spec (n : ℕ) (ε : Fin n → Bool) :
    (∀ β : ℝ, β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) (gaussDens ε β) β ∧
      0 ≤ gaussDens ε β) ∧ ContinuousOn (gaussDens ε) {β | β ≠ 0} ∧
      ∀ s : Bool, (∃ a, ε a = s) → 0 < gaussDens ε (sgn ℝ s) := by
  refine ⟨fun β hβ => ⟨(differentiableAt_cdf ε hβ).hasDerivAt, (cdf_mono ε).deriv_nonneg⟩,
    continuousOn_gaussDens ε, ?_⟩
  rintro s ⟨a, rfl⟩
  obtain _ | n := n
  · exact a.elim0
  have hs : sgn ℝ (ε a) ≠ 0 := by unfold sgn; split_ifs <;> simp
  show 0 < deriv (cdf ε) _
  rw [(hasDerivAt_cdf_succ ε a (differentiableAt_cdf _ hs).continuousAt).deriv]
  exact mul_pos Real.pi_pos (expAvg_pos (cdf_mono _) (abs_cdf_le _) _ (cdf_lt _))

end GlobalTheory.GaussMean.Density
