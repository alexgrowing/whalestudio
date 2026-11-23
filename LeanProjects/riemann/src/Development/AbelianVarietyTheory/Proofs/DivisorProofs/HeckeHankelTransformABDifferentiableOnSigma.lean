import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoAB

open MeasureTheory GlobalTheory.HeckeTwoC

def wt (y t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I

def L (y t : ℝ) : ℝ := Real.log |y| + lg (t / y)

theorem wt_eq {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t = (y : ℂ) * (((t / y : ℝ) : ℂ) + I) := by
  unfold wt
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  push_cast
  field_simp

theorem norm_wt {y : ℝ} (hy : y ≠ 0) (t : ℝ) : ‖wt y t‖ = Real.exp (L y t) := by
  rw [wt_eq hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, L, Real.exp_add,
    Real.exp_log (abs_pos.2 hy), ← norm_tI_eq]

theorem wt_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp [wt] at this; exact hy this

def F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b * Complex.exp ((L y t : ℂ) * (-2 * σ)) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def F' (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b *
    (Complex.exp ((L y t : ℂ) * (-2 * σ)) * ((L y t : ℂ) * (-2))) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_eq (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (fun σ => hTransAB a b σ ν y) = fun σ => ∫ t, F a b ν y σ t := by
  funext σ
  unfold hTransAB F
  congr 1; funext t
  congr 2
  rw [show (t : ℂ) + (y : ℂ) * I = wt y t from rfl, norm_wt hy,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]

theorem norm_e (ν t : ℝ) : ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem norm_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) := by
  unfold F
  rw [norm_mul, norm_mul, norm_mul, norm_e, norm_pow, norm_pow, norm_inv, norm_inv, Complex.norm_conj,
    norm_wt hy, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F' a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|) := by
  have : F' a b ν y σ t = F a b ν y σ t * ((L y t : ℂ) * (-2)) := by unfold F F'; ring
  rw [this, norm_mul, norm_F a b ν hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp; ring

theorem bound_exp {ε M c L0 D : ℝ} (hc : 1 + 2 * ε ≤ c) (hM : c ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.exp (-c * (L0 + D)) ≤ Real.exp (M * |L0|) * Real.exp (-(1 + ε) * D) * Real.exp (-(ε * D)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := le_abs_self L0
  have h2 := neg_abs_le L0
  have h3 := abs_nonneg L0
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : 0 ≤ |L0| + L0),
    mul_nonneg (by linarith : 0 ≤ M - c) h3, mul_nonneg (by linarith : 0 ≤ c - 1 - 2 * ε) hD]

theorem bound_F {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F a b ν y σ t‖ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F a b ν hy]
  have hD := lg_nonneg (t / y)
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have h2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) := h
    _ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _

theorem bound_F' {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F' a b ν y σ t‖ ≤
      2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F' a b ν hy]
  have hD : 0 ≤ lg (t / y) := lg_nonneg _
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have hL : |L y t| ≤ |Real.log (abs y)| + lg (t / y) := by
    unfold L; exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hD])
  have hE2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE2D : Real.exp (-(ε * lg (t / y))) * lg (t / y) ≤ 1 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg (t / y))
    have := Real.add_one_le_exp (ε * lg (t / y))
    rw [show (Real.exp (ε * lg (t / y)))⁻¹ * lg (t / y) * ε = (ε * lg (t / y)) / Real.exp (ε * lg (t / y)) by
      field_simp]
    rw [div_le_iff₀ hp]; linarith
  have heC : 0 ≤ Real.exp (M * |Real.log (abs y)|) := (Real.exp_pos _).le
  have hE1 : 0 ≤ Real.exp (-(1 + ε) * lg (t / y)) := (Real.exp_pos _).le
  have hE2p : 0 ≤ Real.exp (-(ε * lg (t / y))) := (Real.exp_pos _).le
  have hl0 := abs_nonneg (Real.log |y|)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) *
          (2 * (|Real.log (abs y)| + lg (t / y))) :=
        mul_le_mul h (by linarith) (by positivity) (by positivity)
    _ = 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) *
          (Real.exp (-(ε * lg (t / y))) * |Real.log (abs y)| + Real.exp (-(ε * lg (t / y))) * lg (t / y)) := by ring
    _ ≤ 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * (1 * |Real.log (abs y)| + 1 / ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hE2 hl0) hE2D) (by positivity)
    _ = _ := by ring

theorem integrable_bound {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : y ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg (t / y))) :=
  (integrable_expL hε).comp_div hy

theorem hasDerivAt_F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) :
    HasDerivAt (fun s => F a b ν y s t) (F' a b ν y σ t) σ := by
  unfold F F'
  have h : HasDerivAt (fun s : ℂ => (L y t : ℂ) * (-2 * s)) ((L y t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (L y t : ℂ)).congr_deriv (by ring)
  exact (h.cexp.const_mul _).mul_const _

theorem continuous_L {y : ℝ} : Continuous (L y) := by
  unfold L
  exact continuous_const.add (continuous_lg.comp (continuous_id.div_const y))

theorem continuous_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F a b ν y σ) := by
  unfold F
  have hw : Continuous (wt y) := by unfold wt; fun_prop
  have h1 : Continuous fun t => (wt y t)⁻¹ := hw.inv₀ (wt_ne hy)
  have h2 : Continuous fun t => ((starRingEnd ℂ) (wt y t))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => (map_ne_zero _).2 (wt_ne hy t))
  have h3 : Continuous fun t => Complex.exp ((L y t : ℂ) * (-2 * σ)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)
  have h4 : Continuous fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by fun_prop
  exact (((h1.pow a).mul (h2.pow b)).mul h3).mul h4

theorem continuous_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F' a b ν y σ) := by
  have : F' a b ν y σ = fun t => F a b ν y σ t * ((L y t : ℂ) * (-2)) := by funext t; unfold F F'; ring
  rw [this]
  exact (continuous_F a b ν hy σ).mul ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)

end GlobalTheory.HeckeTwoAB

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB

theorem hTransAB_differentiableOn : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 →
    DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  intro a b ν y hab hy
  rw [hTransAB_eq a b ν hy]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hab' : (2 : ℝ) ≤ (a + b : ℝ) := by exact_mod_cast hab
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re ∧ σ.re ≤ σ₀.re + ε := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := abs_lt.1 (lt_of_le_of_lt h1 h2)
    simp only [sub_re] at h3
    constructor <;> linarith [h3.1, h3.2]
  set M := (a + b : ℝ) + 2 * (σ₀.re + ε) with hM_def
  have hc : ∀ σ ∈ Metric.ball σ₀ ε, 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re := by
    intro σ hσ; have := (hball σ hσ).1; linarith
  have hM : ∀ σ ∈ Metric.ball σ₀ ε, (a + b : ℝ) + 2 * σ.re ≤ M := by
    intro σ hσ; have := (hball σ hσ).2; rw [hM_def]; linarith
  have h0 := Metric.mem_ball_self hε (x := σ₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F a b ν y)
    (F' := F' a b ν y) (x₀ := σ₀)
    (bound := fun t => 2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) *
      Real.exp (-(1 + ε) * lg (t / y)))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_F a b ν hy σ).aestronglyMeasurable)
    (((integrable_bound hε hy).const_mul (Real.exp (M * |Real.log (abs y)|))).mono'
      (continuous_F a b ν hy σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_F hε a b ν hy (hc σ₀ h0) (hM σ₀ h0) t))
    (continuous_F' a b ν hy σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_F' hε a b ν hy (hc σ hσ) (hM σ hσ) t)
    ((integrable_bound hε hy).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_F a b ν y σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
