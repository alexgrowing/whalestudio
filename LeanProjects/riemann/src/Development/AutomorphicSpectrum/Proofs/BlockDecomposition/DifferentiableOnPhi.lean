import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open MeasureTheory Complex Filter Topology
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

noncomputable def maj (σ t : ℝ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-σ / 2)

theorem integrable_maj {σ : ℝ} (h : 1 < σ) : Integrable (maj σ) := by
  have : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < σ := by simpa using h
  exact integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) this

theorem maj_nonneg (σ t : ℝ) : 0 ≤ maj σ t := by
  unfold maj; positivity

theorem maj_anti {σ τ : ℝ} (h : σ ≤ τ) (t : ℝ) : maj τ t ≤ maj σ t := by
  unfold maj
  apply Real.rpow_le_rpow_of_exponent_le
  · nlinarith [sq_nonneg ‖t‖]
  · linarith

theorem norm_KK (a b : ℝ) (s : ℂ) (t : ℝ) :
    ‖KK (s / 2 + a) (s / 2 + b) 1 t‖ = maj (s.re + a + b) t := by
  set w : ℂ := 1 + I * t with hw
  have hc : (1 : ℂ) - I * t = (starRingEnd ℂ) w := by simp [hw, sub_eq_add_neg]
  have hwre : w.re = 1 := by simp [hw]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwre
  have hc0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw0
  have hn : ‖w‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hw]
    ring
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hargpi : arg w ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  have harg : arg ((starRingEnd ℂ) w) = - arg w := by
    rw [Complex.arg_conj, if_neg hargpi]
  unfold KK maj
  rw [norm_mul, Complex.ofReal_one, hc, ← hw, norm_cpow_of_ne_zero hc0, norm_cpow_of_ne_zero hw0,
    Complex.norm_conj, harg, ← hn]
  have e1 : (-(s / 2 + (a : ℂ))).re = -(s.re / 2 + a) := by simp
  have e2 : (-(s / 2 + (b : ℂ))).re = -(s.re / 2 + b) := by simp
  have e3 : (-(s / 2 + (a : ℂ))).im = -(s.im / 2) := by simp
  have e4 : (-(s / 2 + (b : ℂ))).im = -(s.im / 2) := by simp
  rw [e1, e2, e3, e4]
  rw [← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_mul hpos.le]
  have e5 : ((2 : ℕ) : ℝ) * (-(s.re + a + b) / 2) = -(s.re / 2 + a) + -(s.re / 2 + b) := by
    push_cast; ring
  rw [e5, Real.rpow_add hpos]
  field_simp
  rw [← Real.exp_add]
  simp

theorem norm_ee (ξ t : ℝ) : ‖ee (-((ξ : ℂ) * t))‖ = 1 := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * I * (-((ξ : ℂ) * t)) = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_ee (ξ : ℝ) : Continuous fun t : ℝ => ee (-((ξ : ℂ) * t)) := by
  unfold ee; fun_prop

theorem continuous_ee' (t : ℝ) : Continuous fun ξ : ℝ => ee (-((ξ : ℂ) * t)) := by
  unfold ee; fun_prop

theorem continuous_KK (α β : ℂ) : Continuous fun t : ℝ => KK α β 1 t := by
  unfold KK
  refine Continuous.mul ?_ ?_
  · refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
    left; simp
  · refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
    left; simp

theorem differentiable_KK (a b t : ℝ) :
    Differentiable ℂ fun s : ℂ => KK (s / 2 + a) (s / 2 + b) 1 t := by
  have h1 : ((1 : ℝ) : ℂ) - I * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : ((1 : ℝ) : ℂ) + I * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  unfold KK
  refine Differentiable.mul ?_ ?_
  · exact Differentiable.const_cpow (by fun_prop) (Or.inl h1)
  · exact Differentiable.const_cpow (by fun_prop) (Or.inl h2)

theorem norm_integrand (a b : ℝ) (s : ℂ) (ξ t : ℝ) :
    ‖KK (s / 2 + a) (s / 2 + b) 1 t * ee (-((ξ : ℂ) * t))‖ = maj (s.re + a + b) t := by
  rw [norm_mul, norm_KK, norm_ee, mul_one]

theorem integrable_KK (a b : ℝ) {s : ℂ} (h : 1 < s.re + a + b) :
    Integrable fun t => KK (s / 2 + a) (s / 2 + b) 1 t :=
  (integrable_maj h).mono' (continuous_KK _ _).aestronglyMeasurable
    (Eventually.of_forall fun t => (norm_KK a b s t).le)

theorem differentiableOn_Phi (a b ξ : ℝ) :
    DifferentiableOn ℂ (fun s : ℂ => Phi (s / 2 + a) (s / 2 + b) ξ) (HP (1 - a - b)) := by
  have hU : IsOpen (HP (1 - a - b)) := isOpen_lt continuous_const Complex.continuous_re
  refine (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun t s => KK (s / 2 + a) (s / 2 + b) 1 t * ee (-((ξ : ℂ) * t))) hU ?_ ?_ ?_).1
  · intro y _
    exact ((continuous_KK _ _).mul (continuous_ee ξ)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    exact ((differentiable_KK a b t).mul_const _).differentiableOn
  · intro x hx
    have hx' : 1 - a - b < x.re := hx
    refine ⟨{y | (x.re + a + b + 1) / 2 < y.re + a + b}, ?_, maj ((x.re + a + b + 1) / 2),
      integrable_maj (by linarith), Eventually.of_forall fun t y hy => ?_⟩
    · refine (isOpen_lt continuous_const (by fun_prop)).mem_nhds ?_
      show (x.re + a + b + 1) / 2 < x.re + a + b
      linarith
    · rw [norm_integrand]
      exact maj_anti (le_of_lt hy) t

theorem continuous_Phi (a b : ℝ) {s : ℂ} (h : 1 < s.re + a + b) :
    Continuous fun ξ : ℝ => Phi (s / 2 + a) (s / 2 + b) ξ := by
  unfold Phi
  refine continuous_of_dominated (bound := maj (s.re + a + b)) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_maj h) ?_
  · exact ((continuous_KK _ _).mul (continuous_ee ξ)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => (norm_integrand a b s ξ t).le
  · exact Eventually.of_forall fun t => continuous_const.mul (continuous_ee' t)

theorem norm_Phi_le (a b : ℝ) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (h : σ ≤ s.re + a + b) (ξ : ℝ) :
    ‖Phi (s / 2 + a) (s / 2 + b) ξ‖ ≤ ∫ t, maj σ t := by
  unfold Phi
  refine norm_integral_le_of_norm_le (integrable_maj hσ) (Eventually.of_forall fun t => ?_)
  rw [norm_integrand]
  exact maj_anti h t

theorem w0 : W0 := by
  intro a b
  refine ⟨fun ξ => differentiableOn_Phi a b ξ, fun s hs => ?_, fun δ B hδ => ?_⟩
  · have hs' : 1 - a - b < s.re := hs
    have h : 1 < s.re + a + b := by linarith
    exact ⟨integrable_KK a b h, continuous_Phi a b h⟩
  · have hC : 0 ≤ ∫ t, maj (1 + δ) t := integral_nonneg fun t => maj_nonneg _ t
    refine ⟨∫ t, maj (1 + δ) t, fun s ξ h1 _ => ?_⟩
    refine (norm_Phi_le a b (σ := 1 + δ) (by linarith) (by linarith) ξ).trans ?_
    refine le_mul_of_one_le_right hC ?_
    exact Real.one_le_exp (by positivity)

end GlobalTheory.CompanionTheory.HalfWeight
