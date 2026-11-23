import Mathlib

open MeasureTheory intervalIntegral Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume

def ee (u t : ℝ) : ℂ := Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))

lemma ee_norm (u t : ℝ) : ‖ee u t‖ = 1 := Complex.norm_exp_I_mul_ofReal (u * t)

lemma ee_cont (u : ℝ) : Continuous (ee u) := by unfold ee; fun_prop

lemma hasDerivAt_V {u : ℝ} (hu : u ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => ee u t / (Complex.I * u)) (ee u t) t := by
  have hIu : Complex.I * (u : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hu)
  have h0 : HasDerivAt (fun t : ℝ => ((u * t : ℝ) : ℂ)) ((u : ℝ) : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul u).ofReal_comp
    simpa using this
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((u * t : ℝ) : ℂ)) (Complex.I * u) t := h0.const_mul Complex.I
  have h3 := h1.cexp.div_const (Complex.I * u)
  exact h3.congr_deriv (by rw [mul_div_assoc, div_self hIu, mul_one]; rfl)

lemma norm_V {u : ℝ} (hu : 0 < u) (t : ℝ) : ‖ee u t / (Complex.I * u)‖ = 1 / u := by
  rw [norm_div, ee_norm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]

lemma ibp2 {φ φ' φ'' : ℝ → ℝ} {α β u : ℝ} (hαβ : α ≤ β) (hu : 0 < u)
    (h1 : ∀ x ∈ uIcc α β, HasDerivAt φ (φ' x) x) (h2 : ∀ x ∈ uIcc α β, HasDerivAt φ' (φ'' x) x)
    (h3 : ContinuousOn φ'' (uIcc α β)) :
    ‖∫ t in α..β, (φ t : ℂ) * ee u t‖ ≤
      (|φ α| + |φ β|) / u + ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 := by
  set V : ℝ → ℂ := fun t => ee u t / (Complex.I * u) with hV
  have hVd : ∀ x ∈ uIcc α β, HasDerivAt V (ee u x) x := fun x _ => hasDerivAt_V hu.ne' x
  have hφ'c : ContinuousOn φ' (uIcc α β) := fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable (fun t => (φ' t : ℂ)) volume α β :=
    (Complex.continuous_ofReal.comp_continuousOn hφ'c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => (φ'' t : ℂ)) volume α β :=
    (Complex.continuous_ofReal.comp_continuousOn h3).intervalIntegrable
  have hie : IntervalIntegrable (ee u) volume α β := (ee_cont u).intervalIntegrable _ _
  have e1 := integral_mul_deriv_eq_deriv_mul (u := fun t => (φ t : ℂ)) (v := V) (u' := fun t => (φ' t : ℂ))
    (v' := ee u) (fun x hx => (h1 x hx).ofReal_comp) hVd hi1 hie
  have e2 := integral_mul_deriv_eq_deriv_mul (u := fun t => (φ' t : ℂ)) (v := V) (u' := fun t => (φ'' t : ℂ))
    (v' := ee u) (fun x hx => (h2 x hx).ofReal_comp) hVd hi2 hie
  have e3 : ∫ t in α..β, (φ' t : ℂ) * V t = (∫ t in α..β, (φ' t : ℂ) * ee u t) / (Complex.I * u) := by
    rw [← intervalIntegral.integral_div]; congr 1; funext t; simp only [hV]; ring
  have hVn := norm_V hu
  have hu2 : 0 < u ^ 2 := by positivity

  have b3 : ‖∫ t in α..β, (φ'' t : ℂ) * V t‖ ≤ (∫ t in α..β, |φ'' t|) / u := by
    refine (intervalIntegral.norm_integral_le_integral_norm hαβ).trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_div]
    congr 1; funext t
    rw [norm_mul, hVn, Complex.norm_real, Real.norm_eq_abs]; ring
  have b2 : ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ ≤ (|φ' α| + |φ' β|) / u + (∫ t in α..β, |φ'' t|) / u := by
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
    rw [norm_mul, norm_mul, hVn, hVn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have := b3
    have e : |φ' β| * (1 / u) + |φ' α| * (1 / u) = (|φ' α| + |φ' β|) / u := by ring
    linarith
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  rw [norm_mul, norm_mul, hVn, hVn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, e3,
    norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have b2' : ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ / u ≤ ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 := by
    rw [div_le_iff₀ hu]
    calc ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ ≤ (|φ' α| + |φ' β|) / u + (∫ t in α..β, |φ'' t|) / u := b2
      _ = ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 * u := by field_simp
  have e : |φ β| * (1 / u) + |φ α| * (1 / u) = (|φ α| + |φ β|) / u := by ring
  linarith

def g0 (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def g1 (t : ℝ) : ℝ := -t / Real.sqrt (1 - t ^ 2)
def g2 (t : ℝ) : ℝ := -1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))

lemma hp1 (t : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * t)) t :=
  ((hasDerivAt_pow 2 t).const_sub 1).congr_deriv (by norm_num)

lemma hasDerivAt_g0 {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g0 (g1 t) t := by
  have hp : 0 < 1 - t ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hp
  have h2 := (hp1 t).sqrt hp.ne'
  have e : g1 t = -(2 * t) / (2 * Real.sqrt (1 - t ^ 2)) := by
    unfold g1; field_simp
  rw [e]; exact h2

lemma hasDerivAt_g1 {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g1 (g2 t) t := by
  have hp : 0 < 1 - t ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hp.le
  have h2 := (hasDerivAt_neg t).div ((hp1 t).sqrt hp.ne') hs.ne'
  have e : g2 t = (-1 * Real.sqrt (1 - t ^ 2) - -t * (-(2 * t) / (2 * Real.sqrt (1 - t ^ 2)))) /
      Real.sqrt (1 - t ^ 2) ^ 2 := by
    unfold g2
    set s := Real.sqrt (1 - t ^ 2)
    rw [hsq]
    field_simp
    nlinarith [hsq]
  rw [e]; exact h2

lemma continuousOn_g2_symmetric_interval {a : ℝ} (ha : a < 1) (ha0 : 0 ≤ a) : ContinuousOn g2 (uIcc (-a) a) := by
  apply ContinuousOn.div continuousOn_const
  · exact ((continuous_const.sub (continuous_id.pow 2)).mul
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))).continuousOn
  · intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    have hp : 0 < 1 - x ^ 2 := by linarith
    exact (mul_pos hp (Real.sqrt_pos.2 hp)).ne'

theorem J_bound {u : ℝ} (hu : 1 ≤ u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by
  have hu0 : 0 < u := by linarith
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsu2 : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  set a : ℝ := 1 - 1 / u with ha
  have hia : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
  have hia0 : 0 < 1 / u := by positivity
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  have hcont : Continuous fun t => (g0 t : ℂ) * ee u t := by
    unfold g0; exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2)))).mul (ee_cont u)
  have hii : ∀ x y : ℝ, IntervalIntegrable (fun t => (g0 t : ℂ) * ee u t) volume x y :=
    fun x y => hcont.intervalIntegrable x y
  rw [← integral_add_adjacent_intervals (hii (-1) (-a)) (hii (-a) 1),
    ← integral_add_adjacent_intervals (hii (-a) a) (hii a 1)]

  have hsq2 : Real.sqrt (2 / u) = Real.sqrt 2 / Real.sqrt u := Real.sqrt_div' 2 hu0.le
  have hend : ∀ t : ℝ, 1 - t ^ 2 ≤ 2 / u → ‖(g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u := by
    intro t ht
    unfold g0
    rw [norm_mul, ee_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← hsq2]
    exact Real.sqrt_le_sqrt ht
  have b1 : ‖∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u * (1 / u) := by
    refine (norm_integral_le_of_norm_le_const fun t ht => hend t ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le (by linarith)] at ht
      have h1 : 0 ≤ 1 + t := by linarith [ht.1]
      have h2 : 1 + t ≤ 1 / u := by linarith [ht.2]
      have h3 : 1 - t ≤ 2 := by linarith [ht.1]
      have : 1 - t ^ 2 = (1 + t) * (1 - t) := by ring
      rw [this, div_eq_mul_one_div 2 u]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]; ring
  have b3 : ‖∫ t in a..1, (g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u * (1 / u) := by
    refine (norm_integral_le_of_norm_le_const fun t ht => hend t ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le (by linarith)] at ht
      have h1 : 0 ≤ 1 - t := by linarith [ht.2]
      have h2 : 1 - t ≤ 1 / u := by linarith [ht.1]
      have h3 : 1 + t ≤ 2 := by linarith [ht.2]
      have : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      rw [this, div_eq_mul_one_div 2 u]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]; ring

  have hin : ∀ x ∈ uIcc (-a) a, x ^ 2 < 1 := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    nlinarith [hx.1, hx.2]
  have b2 := ibp2 (φ := g0) (φ' := g1) (φ'' := g2) (α := -a) (β := a) (by linarith) hu0
    (fun x hx => hasDerivAt_g0 (hin x hx)) (fun x hx => hasDerivAt_g1 (hin x hx)) (continuousOn_g2_symmetric_interval ha1 ha0)

  have hpa : 0 < 1 - a ^ 2 := by nlinarith
  set s := Real.sqrt (1 - a ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpa
  have hslo : 1 / Real.sqrt u ≤ s := by
    have e1 : 1 / Real.sqrt u = Real.sqrt (1 / u) := by rw [Real.sqrt_div' 1 hu0.le, Real.sqrt_one]
    rw [hs, e1]
    apply Real.sqrt_le_sqrt
    rw [ha]
    have : 1 - (1 - 1 / u) ^ 2 = 1 / u * (2 - 1 / u) := by ring
    rw [this]
    nlinarith
  have hshi : s ≤ Real.sqrt 2 / Real.sqrt u := by
    rw [hs, ← hsq2]
    apply Real.sqrt_le_sqrt
    rw [ha]
    have : 1 - (1 - 1 / u) ^ 2 = 1 / u * (2 - 1 / u) := by ring
    rw [this, div_eq_mul_one_div 2 u]
    nlinarith
  have hg0a : |g0 (-a)| + |g0 a| ≤ 2 * (Real.sqrt 2 / Real.sqrt u) := by
    simp only [g0, neg_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← hs]; linarith
  have hinv : 1 / s ≤ Real.sqrt u := by
    rw [div_le_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left hslo hsu.le
    rw [mul_one_div_cancel hsu.ne'] at this
    linarith
  have hg1a : |g1 (-a)| + |g1 a| ≤ 2 * Real.sqrt u := by
    simp only [g1, neg_sq, neg_neg, abs_div, abs_neg, abs_of_nonneg ha0, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← hs]
    have : a / s ≤ 1 / s := div_le_div_of_nonneg_right (by linarith) hs0.le
    linarith

  have hint : ∫ t in (-a)..a, |g2 t| = 2 * (a / s) := by
    have e : ∫ t in (-a)..a, |g2 t| = ∫ t in (-a)..a, -g2 t := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx2 := hin x hx
      have hp : 0 < 1 - x ^ 2 := by linarith
      have : g2 x ≤ 0 := by
        simp only [g2]
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hp.le (Real.sqrt_nonneg _))
      simp only
      rw [abs_of_nonpos this]
    rw [e, intervalIntegral.integral_neg, integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_g1 (hin x hx))
      ((continuousOn_g2_symmetric_interval ha1 ha0).intervalIntegrable)]
    simp only [g1, neg_sq, neg_neg]
    rw [← hs]; ring
  have hint' : ∫ t in (-a)..a, |g2 t| ≤ 2 * Real.sqrt u := by
    rw [hint]
    have : a / s ≤ 1 / s := div_le_div_of_nonneg_right (by linarith) hs0.le
    linarith

  have hm : ‖∫ t in (-a)..a, (g0 t : ℂ) * ee u t‖ ≤ (2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by
    refine b2.trans ?_
    have k1 : (|g0 (-a)| + |g0 a|) / u ≤ 2 * Real.sqrt 2 / (u * Real.sqrt u) := by
      rw [div_le_div_iff₀ hu0 (by positivity)]
      have := mul_le_mul_of_nonneg_right hg0a (by positivity : 0 ≤ u * Real.sqrt u)
      calc (|g0 (-a)| + |g0 a|) * (u * Real.sqrt u) ≤ 2 * (Real.sqrt 2 / Real.sqrt u) * (u * Real.sqrt u) := this
        _ = 2 * Real.sqrt 2 * u := by field_simp
    have k2 : ((|g1 (-a)| + |g1 a|) + ∫ t in (-a)..a, |g2 t|) / u ^ 2 ≤ 4 / (u * Real.sqrt u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := add_le_add hg1a hint'
      have h4 := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ u * Real.sqrt u)
      calc ((|g1 (-a)| + |g1 a|) + ∫ t in (-a)..a, |g2 t|) * (u * Real.sqrt u)
          ≤ (2 * Real.sqrt u + 2 * Real.sqrt u) * (u * Real.sqrt u) := h4
        _ = 4 * u ^ 2 := by rw [show (2 * Real.sqrt u + 2 * Real.sqrt u) * (u * Real.sqrt u) =
              4 * u * (Real.sqrt u * Real.sqrt u) by ring, hsu2]; ring
    have : 2 * Real.sqrt 2 / (u * Real.sqrt u) + 4 / (u * Real.sqrt u) = (2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by
      ring
    linarith
  have hends : Real.sqrt 2 / Real.sqrt u * (1 / u) = Real.sqrt 2 / (u * Real.sqrt u) := by field_simp
  have h22 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc ‖(∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t) + ((∫ t in (-a)..a, (g0 t : ℂ) * ee u t) +
        ∫ t in a..1, (g0 t : ℂ) * ee u t)‖
      ≤ ‖∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t‖ + (‖∫ t in (-a)..a, (g0 t : ℂ) * ee u t‖ +
        ‖∫ t in a..1, (g0 t : ℂ) * ee u t‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ Real.sqrt 2 / (u * Real.sqrt u) + ((2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) +
        Real.sqrt 2 / (u * Real.sqrt u)) := by rw [← hends]; gcongr
    _ = (4 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by ring
    _ ≤ 10 / (u * Real.sqrt u) := by
        apply div_le_div_of_nonneg_right _ (by positivity); linarith

end Formalism.FourierDecayAlt.P.DiscFubiniVolume
