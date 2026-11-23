import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoDY

open MeasureTheory

def wt (t y : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I

def igE (a b : ℕ) (σ : ℂ) (ν y t : ℝ) : ℂ :=
  (wt t y)⁻¹ ^ a * ((starRingEnd ℂ) (wt t y))⁻¹ ^ b *
    Complex.exp ((Real.log (t ^ 2 + y ^ 2) : ℂ) * (-σ)) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem q_pos {t y : ℝ} (hy : y ≠ 0) : 0 < t ^ 2 + y ^ 2 := by
  have : 0 < y ^ 2 := by positivity
  nlinarith [sq_nonneg t]

theorem wt_ne {t y : ℝ} (hy : y ≠ 0) : wt t y ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp [wt] at this; exact hy this

theorem conj_wt (t y : ℝ) : (starRingEnd ℂ) (wt t y) = (t : ℂ) + (y : ℂ) * (-I) := by
  simp [wt, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]

theorem conj_wt_ne {t y : ℝ} (hy : y ≠ 0) : (starRingEnd ℂ) (wt t y) ≠ 0 := by
  rw [map_ne_zero]; exact wt_ne hy

theorem norm_wt (t y : ℝ) : ‖wt t y‖ = √(t ^ 2 + y ^ 2) := Complex.norm_add_mul_I t y

theorem cpow_eq {t y : ℝ} (hy : y ≠ 0) (σ : ℂ) :
    ((‖wt t y‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp ((Real.log (t ^ 2 + y ^ 2) : ℂ) * (-σ)) := by
  have hq := q_pos (t := t) hy
  have hn : (0 : ℝ) < ‖wt t y‖ := norm_pos_iff.2 (wt_ne hy)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  congr 1
  have : Real.log (t ^ 2 + y ^ 2) = 2 * Real.log ‖wt t y‖ := by
    rw [norm_wt, Real.log_sqrt hq.le]; ring
  rw [this]; push_cast; ring

theorem hTransAB_eq {a b : ℕ} {σ : ℂ} {ν y : ℝ} (hy : y ≠ 0) : hTransAB a b σ ν y = ∫ t, igE a b σ ν y t := by
  unfold hTransAB igE
  congr 1; funext t
  rw [← cpow_eq hy σ]; rfl

theorem norm_igE {a b : ℕ} {σ : ℂ} {ν y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖igE a b σ ν y t‖ = Real.exp (-(((a : ℝ) + b + 2 * σ.re) / 2) * Real.log (t ^ 2 + y ^ 2)) := by
  have hq := q_pos (t := t) hy
  have hs : √(t ^ 2 + y ^ 2) = Real.exp (Real.log (t ^ 2 + y ^ 2) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]; ring_nf
  unfold igE
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, Complex.norm_conj, norm_wt, hs,
    Complex.norm_exp, Complex.norm_exp]
  have h0 : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
  rw [h0, Real.exp_zero, mul_one, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring

end GlobalTheory.HeckeTwoDY

noncomputable section
namespace GlobalTheory.HeckeTwoDY
open MeasureTheory

theorem hasDerivAt_wt (t y : ℝ) : HasDerivAt (fun y' : ℝ => wt t y') I y := by
  unfold wt
  simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (t : ℂ)

theorem hasDerivAt_cwt (t y : ℝ) : HasDerivAt (fun y' : ℝ => (starRingEnd ℂ) (wt t y')) (-I) y := by
  have : (fun y' : ℝ => (starRingEnd ℂ) (wt t y')) = fun y' : ℝ => (t : ℂ) + (y' : ℂ) * (-I) := by
    funext y'; exact conj_wt t y'
  rw [this]
  simpa using ((hasDerivAt_id y).ofReal_comp.mul_const (-I)).const_add (t : ℂ)

theorem hasDerivAt_invpow {f : ℝ → ℂ} {c : ℂ} {y : ℝ} (hf : HasDerivAt f c y) (hne : f y ≠ 0) (n : ℕ) :
    HasDerivAt (fun y' => (f y')⁻¹ ^ n) (-(n : ℂ) * c * (f y)⁻¹ ^ (n + 1)) y := by
  have hz := (hasDerivAt_zpow (-(n : ℤ)) (f y) (Or.inl hne)).comp y hf
  have hfun : (fun y' => (f y')⁻¹ ^ n) = (fun x : ℂ => x ^ (-(n : ℤ))) ∘ f := by
    funext y'; simp [Function.comp, zpow_neg, inv_pow]
  rw [hfun]
  refine hz.congr_deriv ?_
  have : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast, inv_pow]; push_cast; ring

theorem two_y_div {t y : ℝ} (hy : y ≠ 0) :
    (((2 * y / (t ^ 2 + y ^ 2) : ℝ)) : ℂ) = I * ((wt t y)⁻¹ - ((starRingEnd ℂ) (wt t y))⁻¹) := by
  have hq := q_pos (t := t) hy
  have hw := wt_ne (t := t) hy
  have hc := conj_wt_ne (t := t) hy
  have hprod : wt t y * (starRingEnd ℂ) (wt t y) = ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    rw [conj_wt]; unfold wt; push_cast; ring_nf; rw [I_sq]; ring
  have hq' : ((t ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [inv_sub_inv hw hc, hprod, conj_wt]
  unfold wt
  push_cast
  field_simp
  ring_nf; rw [I_sq]; ring

theorem hasDerivAt_igE (a b : ℕ) (σ : ℂ) (ν t : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y' => igE a b σ ν y' t)
      (I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y t + I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y t) y := by
  have hA := hasDerivAt_invpow (hasDerivAt_wt t y) (wt_ne hy) a
  have hB := hasDerivAt_invpow (hasDerivAt_cwt t y) (conj_wt_ne hy) b
  have hq : HasDerivAt (fun y' : ℝ => t ^ 2 + y' ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (t ^ 2)
  have hL := (((hq.log (q_pos hy).ne').ofReal_comp).mul_const (-σ)).cexp
  have h := ((hA.mul hB).mul hL).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  unfold igE
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [two_y_div hy]
  ring

end GlobalTheory.HeckeTwoDY

noncomputable section
namespace GlobalTheory.HeckeTwoDY
open MeasureTheory

theorem integrable_bd {k c : ℝ} (hk : 1 < k) (hc : c ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-(k / 2) * Real.log (t ^ 2 + c ^ 2))) := by
  have h := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := k) (by simp; linarith)).comp_div hc
  have h2 := h.const_mul ((c ^ 2) ^ (-k / 2))
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  have hc2 : 0 < c ^ 2 := by positivity
  have he : c ^ 2 * (1 + ‖t / c‖ ^ 2) = t ^ 2 + c ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs, div_pow]; field_simp; ring
  simp only
  rw [← Real.mul_rpow hc2.le (by positivity), he, Real.rpow_def_of_pos (by positivity)]
  congr 1; ring

theorem continuous_igE (a b : ℕ) (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : Continuous (fun t => igE a b σ ν y t) := by
  unfold igE
  have hw : Continuous fun t : ℝ => wt t y := by unfold wt; fun_prop
  have h1 : Continuous fun t : ℝ => (wt t y)⁻¹ := hw.inv₀ (fun t => wt_ne hy)
  have h2 : Continuous fun t : ℝ => ((starRingEnd ℂ) (wt t y))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => conj_wt_ne hy)
  have h3 : Continuous fun t : ℝ => Real.log (t ^ 2 + y ^ 2) :=
    (by fun_prop : Continuous fun t : ℝ => t ^ 2 + y ^ 2).log (fun t => (q_pos hy).ne')
  exact (((h1.pow a).mul (h2.pow b)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp h3).mul continuous_const))).mul (by fun_prop)

theorem integrable_igE {a b : ℕ} {σ : ℂ} (ν : ℝ) {y : ℝ} (hab : 2 ≤ a + b) (hσ : -1 / 2 < σ.re) (hy : y ≠ 0) :
    Integrable (fun t => igE a b σ ν y t) := by
  have hab' : (2 : ℝ) ≤ a + b := by exact_mod_cast hab
  exact (integrable_bd (k := (a : ℝ) + b + 2 * σ.re) (by linarith) hy).mono'
    (continuous_igE a b σ ν hy).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (norm_igE hy t).le)

theorem norm_igE_le {a b : ℕ} {σ : ℂ} {ν y y' : ℝ} (hk : 0 ≤ (a : ℝ) + b + 2 * σ.re) (hy : y ≠ 0)
    (hy' : |y' - y| < |y| / 2) (t : ℝ) :
    ‖igE a b σ ν y' t‖ ≤ Real.exp (-(((a : ℝ) + b + 2 * σ.re) / 2) * Real.log (t ^ 2 + (y / 2) ^ 2)) := by
  have h1 : |y| / 2 < |y'| := by
    have := abs_sub_abs_le_abs_sub y y'
    rw [abs_sub_comm] at this; linarith
  have hypos : 0 < |y| := abs_pos.2 hy
  have hy'0 : y' ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith
  have h2 : (y / 2) ^ 2 ≤ y' ^ 2 := by
    rw [← sq_abs y', show (y / 2) ^ 2 = (|y| / 2) ^ 2 by rw [div_pow, div_pow, sq_abs]]
    nlinarith
  have hq0 : 0 < t ^ 2 + (y / 2) ^ 2 := q_pos (div_ne_zero hy two_ne_zero)
  have hlog : Real.log (t ^ 2 + (y / 2) ^ 2) ≤ Real.log (t ^ 2 + y' ^ 2) := Real.log_le_log hq0 (by linarith)
  rw [norm_igE hy'0]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hlog hk]

end GlobalTheory.HeckeTwoDY

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoDY

theorem hTransAB_hasDerivAt : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by
  intro a b σ ν y hab hσ hy
  have hre : -1 / 2 < σ.re := hσ
  have hab' : (2 : ℝ) ≤ a + b := by exact_mod_cast hab
  have hypos : 0 < |y| := abs_pos.2 hy
  have hε : 0 < |y| / 2 := by linarith
  have hball : ∀ y' ∈ Metric.ball y (|y| / 2), |y' - y| < |y| / 2 := fun y' h => by
    simpa [Metric.mem_ball, Real.dist_eq] using h
  have hne : ∀ y' ∈ Metric.ball y (|y| / 2), y' ≠ 0 := fun y' h => by
    have h0 := hball y' h
    intro e; rw [e, zero_sub, abs_neg] at h0; linarith
  have hy2 : y / 2 ≠ 0 := div_ne_zero hy two_ne_zero
  have hk : 0 ≤ ((a + 1 : ℕ) : ℝ) + b + 2 * σ.re := by push_cast; linarith
  have hk' : 0 ≤ (a : ℝ) + ((b + 1 : ℕ) : ℝ) + 2 * σ.re := by push_cast; linarith
  have e1 : ((a + 1 : ℕ) : ℝ) + b + 2 * σ.re = (a : ℝ) + b + 2 * σ.re + 1 := by push_cast; ring
  have e2 : (a : ℝ) + ((b + 1 : ℕ) : ℝ) + 2 * σ.re = (a : ℝ) + b + 2 * σ.re + 1 := by push_cast; ring
  set k := (a : ℝ) + b + 2 * σ.re with hk_def
  have hint1 := integrable_igE ν (a := a + 1) (b := b) (by omega) hre hy
  have hint2 := integrable_igE ν (a := a) (b := b + 1) (by omega) hre hy
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y' t => igE a b σ ν y' t)
    (F' := fun y' t => I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y' t + I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y' t)
    (x₀ := y)
    (bound := fun t => (‖-(a : ℂ) - σ‖ + ‖(b : ℂ) + σ‖) * Real.exp (-((k + 1) / 2) * Real.log (t ^ 2 + (y / 2) ^ 2)))
    (Metric.ball_mem_nhds y hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) fun y' h => (continuous_igE a b σ ν (hne y' h)).aestronglyMeasurable)
    (integrable_igE ν hab hre hy)
    (((continuous_igE (a + 1) b σ ν hy).const_mul _).add ((continuous_igE a (b + 1) σ ν hy).const_mul _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t y' hy' => by
      have b1 := norm_igE_le (ν := ν) hk hy (hball y' hy') t
      have b2 := norm_igE_le (ν := ν) hk' hy (hball y' hy') t
      rw [e1] at b1; rw [e2] at b2
      calc _ ≤ ‖I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y' t‖ + ‖I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y' t‖ := norm_add_le _ _
        _ = ‖-(a : ℂ) - σ‖ * ‖igE (a + 1) b σ ν y' t‖ + ‖(b : ℂ) + σ‖ * ‖igE a (b + 1) σ ν y' t‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
        _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left b1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left b2 (norm_nonneg _)))
    ((integrable_bd (k := k + 1) (by linarith) hy2).const_mul _)
    (Filter.Eventually.of_forall fun t y' hy' => hasDerivAt_igE a b σ ν t (hne y' hy'))
  have hfun : (fun y' : ℝ => hTransAB a b σ ν y') =ᶠ[nhds y] fun y' => ∫ t, igE a b σ ν y' t :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) fun y' h => hTransAB_eq (hne y' h)
  refine (key.2.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul,
    hTransAB_eq hy, hTransAB_eq hy]

end GlobalTheory.HeckeTwo
