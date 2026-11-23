import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideMore
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RealTh

def gE (A B u : ℂ) : ℂ := Complex.exp (-A * (u * conj u) + B * (u + conj u))

theorem continuous_gE (A B : ℂ) : Continuous (gE A B) := by
  unfold gE
  fun_prop

theorem norm_gE (A : ℂ) (β : ℝ) (u : ℂ) :
    ‖gE A (Complex.I * β) u‖ = Real.exp (-A.re * ‖u‖ ^ 2) := by
  have h1 : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : u + conj u = ((2 * u.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  rw [gE, Complex.norm_exp, h1, h2]
  congr 1
  generalize ‖u‖ ^ 2 = x
  generalize 2 * u.re = y
  simp

theorem integrable_norm_pow_gauss {α : ℝ} (hα : 0 < α) (k : ℕ) :
    Integrable (fun u : ℂ => ‖u‖ ^ k * Real.exp (-α * ‖u‖ ^ 2)) := by
  have hs : 0 < Real.sqrt (α / Real.pi) := Real.sqrt_pos.mpr (div_pos hα Real.pi_pos)
  let G : SchwartzMap ℂ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℂ (Real.sqrt (α / Real.pi)) hs.ne').toContinuousLinearEquiv
    (gaussianSchwartz ℂ)
  have hG : ∀ u, ‖G u‖ = Real.exp (-α * ‖u‖ ^ 2) := by
    intro u
    have hsq : Real.sqrt (α / Real.pi) ^ 2 = α / Real.pi := Real.sq_sqrt (div_pos hα Real.pi_pos).le
    have hn : ‖(Real.sqrt (α / Real.pi) : ℝ) • u‖ ^ 2 = α / Real.pi * ‖u‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsq]
    simp only [G, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      gaussianSchwartz_apply]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hn]
    congr 1
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  have := G.integrable_pow_mul (volume : Measure ℂ) k
  simpa only [hG] using this

theorem integrable_mono_gE (A : ℂ) (hA : 0 < A.re) (β : ℝ) (k l : ℕ) :
    Integrable (fun u : ℂ => conj u ^ k * u ^ l * gE A (Complex.I * β) u) := by
  refine (integrable_norm_pow_gauss hA (k + l)).mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · have := continuous_gE A (Complex.I * β)
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_gE, pow_add]

theorem lineDeriv_conj_pow (m : ℕ) (u v : ℂ) :
    HasLineDerivAt ℝ (fun u : ℂ => conj u ^ m) ((m : ℂ) * conj u ^ (m - 1) * conj v) u v := by
  have h0 : HasDerivAt (fun t : ℝ => conj u + (t : ℂ) * conj v) (conj v) 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (conj v)).const_add (conj u)
    simpa using this
  have h1 := h0.fun_pow m
  unfold HasLineDerivAt
  have h2 : (fun t : ℝ => conj (u + t • v) ^ m) = fun t : ℝ => (conj u + (t : ℂ) * conj v) ^ m := by
    funext t
    simp [Complex.real_smul]
  rw [h2]
  simpa using h1

theorem lineDeriv_gE (A B u v : ℂ) :
    HasLineDerivAt ℝ (gE A B)
      (gE A B u * (-A * (v * conj u + u * conj v) + B * (v + conj v))) u v := by
  have hw : HasDerivAt (fun t : ℝ => u + (t : ℂ) * v) v 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const v).const_add u
    simpa using this
  have hc : HasDerivAt (fun t : ℝ => conj u + (t : ℂ) * conj v) (conj v) 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (conj v)).const_add (conj u)
    simpa using this
  have h1 := (((hw.fun_mul hc).const_mul (-A)).fun_add ((hw.fun_add hc).const_mul B)).cexp
  unfold HasLineDerivAt
  have h2 : (fun t : ℝ => gE A B (u + t • v)) = fun t : ℝ =>
      Complex.exp (-A * ((u + (t : ℂ) * v) * (conj u + (t : ℂ) * conj v)) +
        B * ((u + (t : ℂ) * v) + (conj u + (t : ℂ) * conj v))) := by
    funext t
    simp [gE, Complex.real_smul]
  rw [h2]
  have h3 : gE A B u * (-A * (v * conj u + u * conj v) + B * (v + conj v)) =
      Complex.exp (-A * ((u + ((0 : ℝ) : ℂ) * v) * (conj u + ((0 : ℝ) : ℂ) * conj v)) +
          B * (u + ((0 : ℝ) : ℂ) * v + (conj u + ((0 : ℝ) : ℂ) * conj v))) *
        (-A * (v * (conj u + ((0 : ℝ) : ℂ) * conj v) + (u + ((0 : ℝ) : ℂ) * v) * conj v) +
          B * (v + conj v)) := by
    simp only [gE, Complex.ofReal_zero, zero_mul, add_zero]
  rw [h3]
  exact h1

theorem integrable_ibp_left (A : ℂ) (hA : 0 < A.re) (β : ℝ) (m : ℕ) (v : ℂ) :
    Integrable (fun u : ℂ => ((m : ℂ) * conj u ^ (m - 1) * conj v) * gE A (Complex.I * β) u) := by
  have := (integrable_mono_gE A hA β (m - 1) 0).const_mul ((m : ℂ) * conj v)
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [pow_zero, mul_one]
  ring

theorem integrable_ibp_right (A : ℂ) (hA : 0 < A.re) (β : ℝ) (m : ℕ) (v : ℂ) :
    Integrable (fun u : ℂ => conj u ^ m * (gE A (Complex.I * β) u *
      (-A * (v * conj u + u * conj v) + (Complex.I * β) * (v + conj v)))) := by
  have h1 := (integrable_mono_gE A hA β (m + 1) 0).const_mul (-A * v)
  have h2 := (integrable_mono_gE A hA β m 1).const_mul (-A * conj v)
  have h3 := (integrable_mono_gE A hA β m 0).const_mul ((Complex.I * β) * (v + conj v))
  refine ((h1.add h2).add h3).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, pow_zero, pow_one, mul_one, pow_succ]
  ring

theorem ibp (A : ℂ) (hA : 0 < A.re) (β : ℝ) (m : ℕ) (v : ℂ) :
    ∫ u : ℂ, conj u ^ m * (gE A (Complex.I * β) u *
        (-A * (v * conj u + u * conj v) + (Complex.I * β) * (v + conj v))) =
      - ∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1) * conj v) * gE A (Complex.I * β) u := by
  have hfg : Integrable (fun u : ℂ => conj u ^ m * gE A (Complex.I * β) u) := by
    simpa using integrable_mono_gE A hA β m 0
  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure ℂ)) (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
    (f := fun u : ℂ => conj u ^ m) (g := gE A (Complex.I * β))
    (f' := fun u => (m : ℂ) * conj u ^ (m - 1) * conj v)
    (g' := fun u => gE A (Complex.I * β) u *
      (-A * (v * conj u + u * conj v) + (Complex.I * β) * (v + conj v)))
    (integrable_ibp_left A hA β m v) (integrable_ibp_right A hA β m v) hfg
    (fun u _ => lineDeriv_conj_pow m u v) (fun u _ => lineDeriv_gE A _ u v)

theorem int3 {f₁ f₂ f₃ : ℂ → ℂ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) (h₃ : Integrable f₃)
    (c₁ c₂ c₃ : ℂ) : ∫ u, (c₁ * f₁ u + c₂ * f₂ u + c₃ * f₃ u) =
      (c₁ * ∫ u, f₁ u) + (c₂ * ∫ u, f₂ u) + (c₃ * ∫ u, f₃ u) := by
  have e := integral_add (f := fun u => c₁ * f₁ u + c₂ * f₂ u) (g := fun u => c₃ * f₃ u)
    ((h₁.const_mul c₁).add (h₂.const_mul c₂)) (h₃.const_mul c₃)
  have e' := integral_add (f := fun u => c₁ * f₁ u) (g := fun u => c₂ * f₂ u)
    (h₁.const_mul c₁) (h₂.const_mul c₂)
  simp only [integral_const_mul] at e e'
  rw [e, e']

def gJ (A : ℂ) (β : ℝ) (m : ℕ) : ℂ := ∫ u : ℂ, conj u ^ m * gE A (Complex.I * β) u

theorem gJ_succ (A : ℂ) (hA : 0 < A.re) (β : ℝ) (m : ℕ) :
    A * gJ A β (m + 1) = (Complex.I * β) * gJ A β m := by
  have h1 := ibp A hA β m 1
  have h2 := ibp A hA β m Complex.I
  have e1 := integrable_ibp_left A hA β m 1
  have a1 : Integrable (fun u : ℂ => conj u ^ (m + 1) * gE A (Complex.I * β) u) := by
    simpa using integrable_mono_gE A hA β (m + 1) 0
  have a2 : Integrable (fun u : ℂ => conj u ^ m * u * gE A (Complex.I * β) u) := by
    simpa using integrable_mono_gE A hA β m 1
  have a3 : Integrable (fun u : ℂ => conj u ^ m * gE A (Complex.I * β) u) := by
    simpa using integrable_mono_gE A hA β m 0
  have s1 : ∫ u : ℂ, conj u ^ m * (gE A (Complex.I * β) u *
        (-A * (1 * conj u + u * conj 1) + (Complex.I * β) * (1 + conj 1))) =
      -A * gJ A β (m + 1) - A * (∫ u : ℂ, conj u ^ m * u * gE A (Complex.I * β) u) +
        2 * (Complex.I * β) * gJ A β m := by
    have := int3 a1 a2 a3 (-A) (-A) (2 * (Complex.I * β))
    rw [gJ, gJ]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
      (this.trans (by ring))
    simp only [map_one, pow_succ]
    ring
  have s2 : ∫ u : ℂ, conj u ^ m * (gE A (Complex.I * β) u *
        (-A * (Complex.I * conj u + u * conj Complex.I) +
          (Complex.I * β) * (Complex.I + conj Complex.I))) =
      -A * Complex.I * gJ A β (m + 1) + A * Complex.I *
        (∫ u : ℂ, conj u ^ m * u * gE A (Complex.I * β) u) := by
    have := int3 a1 a2 a3 (-A * Complex.I) (A * Complex.I) 0
    rw [gJ]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
      (this.trans (by ring))
    simp only [Complex.conj_I, pow_succ]
    ring
  have t1 : ∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1) * conj 1) * gE A (Complex.I * β) u =
      ∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1)) * gE A (Complex.I * β) u := by
    simp
  have t2 : ∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1) * conj Complex.I) * gE A (Complex.I * β) u =
      -Complex.I * ∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1)) * gE A (Complex.I * β) u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.conj_I]
    ring
  rw [s1, t1] at h1
  rw [s2, t2] at h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  generalize (∫ u : ℂ, conj u ^ m * u * gE A (Complex.I * β) u) = K at h1 h2
  generalize (∫ u : ℂ, ((m : ℂ) * conj u ^ (m - 1)) * gE A (Complex.I * β) u) = T at h1 h2
  linear_combination (-1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
    ((A * gJ A β (m + 1) - A * K + T) / 2) * hI

theorem gJ_zero (A : ℂ) (hA : 0 < A.re) (β : ℝ) :
    gJ A β 0 = (Real.pi / A) * Complex.exp ((Complex.I * β) ^ 2 / A) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hA (2 * (Complex.I * β)) (1 : ℂ)
  have hfr : ((Module.finrank ℝ ℂ : ℂ) / 2) = 1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  rw [hfr, Complex.cpow_one] at h
  have e : (2 * (Complex.I * β)) ^ 2 * (‖(1 : ℂ)‖ : ℂ) ^ 2 / (4 * A) = (Complex.I * β) ^ 2 / A := by
    have : A ≠ 0 := fun h0 => by simp [h0] at hA
    simp only [norm_one, Complex.ofReal_one, one_pow, mul_one]
    field_simp
    ring
  rw [e] at h
  rw [gJ, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [pow_zero, one_mul, gE]
  congr 1
  rw [Complex.mul_conj, Complex.add_conj, Complex.normSq_eq_norm_sq]
  simp [Complex.inner]
  ring

theorem gJ_eq (A : ℂ) (hA : 0 < A.re) (β : ℝ) (m : ℕ) :
    gJ A β m = (Real.pi / A) * ((Complex.I * β) / A) ^ m * Complex.exp ((Complex.I * β) ^ 2 / A) := by
  have hA0 : A ≠ 0 := fun h0 => by simp [h0] at hA
  induction m with
  | zero => simpa using gJ_zero A hA β
  | succ m ih =>
    have := gJ_succ A hA β m
    rw [ih] at this
    have e : gJ A β (m + 1) = A⁻¹ * (A * gJ A β (m + 1)) := by
      rw [inv_mul_cancel_left₀ hA0]
    rw [e, this]
    ring

theorem gJ_conj (A : ℂ) (β : ℝ) (m : ℕ) :
    ∫ u : ℂ, u ^ m * gE A (Complex.I * β) u = gJ A β m := by
  rw [gJ, ← (Complex.conjLIE.measurePreserving).integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.conjLIE_apply, Complex.conj_conj, gE]
  congr 2
  ring

def gA (c d r : ℝ) : ℂ := 2 * Real.pi * ((r : ℂ) ^ 2 - Complex.I * (d : ℂ) / (c : ℂ))

theorem gA_re (c d r : ℝ) (hr : 0 < r) : 0 < (gA c d r).re := by
  have e : gA c d r = ((2 * Real.pi * r ^ 2 : ℝ) : ℂ) + ((-(2 * Real.pi) * d / c : ℝ) : ℂ) * Complex.I := by
    unfold gA
    push_cast
    ring
  rw [e]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  positivity

theorem sgR_neg_mul (c : ℝ) (hc : c ≠ 0) : sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) = -(c : ℂ)⁻¹ := by
  unfold sgR
  rcases lt_or_gt_of_ne hc with h | h
  · rw [if_pos (by linarith), abs_of_neg h]
    push_cast
    rw [inv_neg]
    ring
  · rw [if_neg (by linarith), abs_of_pos h]
    push_cast
    ring

theorem sgR_mul_abs (a : ℝ) (ha : a ≠ 0) : sgR a * ((|a| : ℝ) : ℂ) = a := by
  unfold sgR
  rcases lt_or_gt_of_ne ha with h | h
  · rw [if_neg (by linarith), abs_of_neg h]
    push_cast
    ring
  · rw [if_pos h, abs_of_pos h]
    simp

theorem phiInf_real (n : ℤ) (x : ℝ) :
    PhiInf n (x : ℂ) = (x : ℂ) ^ n.natAbs * Complex.exp (-2 * Real.pi * ((x ^ 2 : ℝ) : ℂ)) := by
  have h : Complex.normSq (x : ℂ) = x ^ 2 := by
    rw [Complex.normSq_ofReal]
    ring
  unfold PhiInf
  rw [h]
  split_ifs <;> simp

theorem exp_combine (a d c r : ℝ) (hc : c ≠ 0) (u : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq 1 + d * Complex.normSq u - 2 * (conj 1 * u).re) / c : ℝ) : ℂ)) *
      Complex.exp (-2 * Real.pi * ((Complex.normSq (u * r) : ℝ) : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / c)) *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi) / c : ℝ) : ℂ)) u := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [gE, ← Complex.exp_add, ← Complex.exp_add, Complex.mul_conj, Complex.add_conj, gA]
  congr 1
  simp only [map_one, one_mul, map_mul, Complex.normSq_ofReal]
  push_cast
  field_simp
  ring

theorem int_phi (n : ℤ) (a d c r : ℝ) (hc : c ≠ 0) :
    ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq 1 + d * Complex.normSq u - 2 * (conj 1 * u).re) / c : ℝ) : ℂ)) *
      PhiInf n (u * r) ∂volC =
    2 * (Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / c)) * (r : ℂ) ^ n.natAbs *
      gJ (gA c d r) (-(2 * Real.pi) / c) n.natAbs) := by
  have e : ∀ u : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq 1 + d * Complex.normSq u - 2 * (conj 1 * u).re) / c : ℝ) : ℂ)) *
      PhiInf n (u * r) =
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / c)) * (r : ℂ) ^ n.natAbs *
      ((if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs) *
        gE (gA c d r) (Complex.I * ((-(2 * Real.pi) / c : ℝ) : ℂ)) u) := by
    intro u
    have h := exp_combine a d c r hc u
    have hp : (if 0 ≤ n then conj (u * r) ^ n.natAbs else (u * r) ^ n.natAbs) =
        (r : ℂ) ^ n.natAbs * (if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs) := by
      split_ifs
      · rw [map_mul, Complex.conj_ofReal, mul_pow]
        ring
      · rw [mul_pow]
        ring
    rw [PhiInf, hp]
    linear_combination ((r : ℂ) ^ n.natAbs *
      (if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs)) * h
  simp only [e]
  rw [volC, integral_smul_measure, integral_const_mul]
  have hint : ∫ u : ℂ, (if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs) *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi) / c : ℝ) : ℂ)) u =
      gJ (gA c d r) (-(2 * Real.pi) / c) n.natAbs := by
    split_ifs
    · rfl
    · exact gJ_conj _ _ _
  rw [hint]
  simp

theorem key_zero (n : ℤ) (a b c d r : ℝ) (hc : c = 0) (hdet : a * d - b * c = 1) :
    (r : ℂ) * rWR a b c d (fun y => PhiInf n (y * r)) 1 =
      (r : ℂ) ^ (n.natAbs + 1) *
        ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)))) := by
  subst hc
  have had : a * d = 1 := by linarith
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hadC : (a : ℂ) * d = 1 := by exact_mod_cast had
  have hdi : (d : ℂ) = (a : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hadC
  have hphi : PhiInf n ((a : ℂ) * 1 * (r : ℂ)) =
      ((a * r : ℝ) : ℂ) ^ n.natAbs * Complex.exp (-2 * Real.pi * (((a * r) ^ 2 : ℝ) : ℂ)) := by
    rw [← phiInf_real]
    push_cast
    rw [mul_one]
  simp only [rWR, if_true, Complex.ofReal_zero, zero_mul, mul_zero, add_zero, map_one, mul_one,
    Complex.normSq_apply, Complex.one_re, Complex.one_im, sub_zero]
  have hsg : sgR a * ((|a| : ℝ) : ℂ) = a := sgR_mul_abs a ha
  rw [mul_assoc (Complex.exp _) (sgR a), hsg]
  rw [show PhiInf n ((a : ℂ) * (r : ℂ)) = PhiInf n ((a : ℂ) * 1 * (r : ℂ)) by rw [mul_one], hphi]
  have e1 : (d : ℂ) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) = (a : ℂ) ^ (n.natAbs + 1) := by
    rw [hdi, _root_.zpow_neg, _root_.inv_zpow, inv_inv, zpow_natCast]
  rw [e1]
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (((a * b : ℝ) : ℂ))) *
      Complex.exp (-2 * Real.pi * (((a * r) ^ 2 : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / d)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hdi]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← e2]
  push_cast
  ring

theorem key_ne (n : ℤ) (a b c d r : ℝ) (hr : 0 < r) (hc : c ≠ 0) (hdet : a * d - b * c = 1) :
    (r : ℂ) * rWR a b c d (fun y => PhiInf n (y * r)) 1 =
      (r : ℂ) ^ (n.natAbs + 1) *
        ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)))) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hAre := gA_re c d r hr
  have hA0 : gA c d r ≠ 0 := fun h0 => by simp [h0] at hAre
  set w : ℂ := (d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2) with hw
  have hAw : gA c d r = -(2 * Real.pi * Complex.I * w) / c := by
    rw [gA, hw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [hAw, h0] at hA0
    simp at hA0
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have h1 : (Real.pi : ℂ) / gA c d r = Complex.I * c / (2 * w) := by
    rw [hAw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
  have h2 : Complex.I * ((-(2 * Real.pi) / c : ℝ) : ℂ) / gA c d r = w⁻¹ := by
    rw [hAw]
    push_cast
    field_simp
  have h3 : (Complex.I * ((-(2 * Real.pi) / c : ℝ) : ℂ)) ^ 2 / gA c d r =
      -(2 * Real.pi * Complex.I) / (c * w) := by
    rw [sq, mul_div_assoc, h2]
    push_cast
    field_simp
  have h4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / c)) *
      Complex.exp (-(2 * Real.pi * Complex.I) / (c * w)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w)) := by
    rw [← Complex.exp_add]
    congr 1
    have e : (a : ℂ) * w - 1 = c * ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) := by
      rw [hw]
      linear_combination hdetC
    have e' : ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w = ((a : ℂ) * w - 1) / (c * w) := by
      rw [e]
      field_simp
    rw [e']
    field_simp
    ring
  have hgJ := gJ_eq (gA c d r) hAre (-(2 * Real.pi) / c) n.natAbs
  rw [h1, h2, h3] at hgJ
  simp only [rWR, if_neg hc]
  rw [int_phi n a d c r hc, hgJ, ← h4, _root_.zpow_neg, zpow_natCast,
    mul_assoc Complex.I (sgR (-c)), sgR_neg_mul c hc]
  generalize Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / c)) = e₁
  generalize Complex.exp (-(2 * Real.pi * Complex.I) / (c * w)) = e₂
  rw [inv_pow]
  field_simp
  rw [Complex.I_sq]
  ring

theorem key (n : ℤ) (a b c d r : ℝ) (hr : 0 < r) (hdet : a * d - b * c = 1) :
    (r : ℂ) * rWR a b c d (fun y => PhiInf n (y * r)) 1 =
      (r : ℂ) ^ (n.natAbs + 1) *
        ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)))) := by
  by_cases hc : c = 0
  · exact key_zero n a b c d r hc hdet
  · exact key_ne n a b c d r hr hc hdet

theorem chC_pos (n : ℤ) (s : ℂ) (r : ℝ) (hr : 0 < r) (h : (r : ℂ) ≠ 0) :
    chC n s (Units.mk0 (r : ℂ) h) = ((r ^ 2 : ℝ) : ℂ) ^ s := by
  have hn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp only [chC, Units.val_mk0, hn]
  rw [div_self h, _root_.one_zpow, one_mul]

end GlobalTheory.CompanionTheory.RealTh
