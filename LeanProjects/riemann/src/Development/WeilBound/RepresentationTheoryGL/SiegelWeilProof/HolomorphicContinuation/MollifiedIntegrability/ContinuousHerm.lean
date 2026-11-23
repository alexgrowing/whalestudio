import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DifferentiableOfTop

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  exact Complex.continuous_re.comp ((continuous_const.add (continuous_herm.matrix_mul continuous_herm)).matrix_det)

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := by
  unfold chr
  fun_prop

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  unfold chr
  rw [Complex.norm_exp]
  simp

theorem abs_log_le (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) : |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : δ * Real.log x ≤ x ^ δ := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    linarith
  have h2 : -δ * Real.log x ≤ x ^ (-δ) := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    linarith
  have p1 := Real.rpow_pos_of_pos hx δ
  have p2 := Real.rpow_pos_of_pos hx (-δ)
  rcases abs_cases (Real.log x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, le_div_iff₀ hδ] <;> nlinarith

theorem rpow_neg_le_add (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have p1 := Real.rpow_pos_of_pos hx (-(a0 - d))
  have p2 := Real.rpow_pos_of_pos hx (-(a0 + d))
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-a) ≤ x ^ (-(a0 - d)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith
  · have : x ^ (-a) ≤ x ^ (-(a0 + d)) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    linarith

theorem rp3 {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [Real.rpow_add hx, Real.rpow_add hx]

theorem dP_pos (hI : Integr) (y : E n) : 0 < dP y := by
  obtain ⟨⟨c0, hc0, hc0le⟩, -⟩ := hI n
  exact lt_of_lt_of_le (mul_pos hc0 (by positivity)) (hc0le y)

theorem norm_term (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by
  rw [norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (dP_pos hI y), Complex.neg_re]

theorem continuous_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (z : ℂ) :
    Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
  have : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) :=
    (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
  exact (this.mul hh).mul (continuous_chr t β)

theorem integ_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) {κ C : ℝ}
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) {z : ℂ} (hz : (n : ℝ) ^ 2 / 2 < z.re + κ) :
    Integrable fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  obtain ⟨-, hint⟩ := hI n
  refine Integrable.mono' ((hint (z.re + κ) hz).const_mul C) (continuous_term hI t β hh z).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_term hI]
  have hp := dP_pos hI y
  calc dP y ^ (-z.re) * ‖h y‖ ≤ dP y ^ (-z.re) * (C * dP y ^ (-κ)) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.rpow_nonneg hp.le _)
    _ = C * dP y ^ (-(z.re + κ)) := by
        rw [neg_add, Real.rpow_add hp]; ring

theorem holo (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (κ C : ℝ)
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y)
      {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + κ} := by
  obtain ⟨-, hint⟩ := hI n
  intro z0 hz0
  simp only [Set.mem_ofPred_eq] at hz0
  set σs := z0.re + κ with hσs
  set δ := (σs - (n : ℝ) ^ 2 / 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb' : ∀ y, ‖h y‖ ≤ C' * dP y ^ (-κ) := fun y =>
    (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (dP_pos hI y).le _))
  let F : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y
  let F' : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
  have hF'c : Continuous (F' z0) := by
    have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
    have h1 : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z0) :=
      (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
    have h2 : Continuous fun y : E n => ((Real.log (dP y) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_dP.log fun y => (dP_pos hI y).ne')
    exact ((h1.mul h2.neg).mul hh).mul (continuous_chr t β)
  let B : E n → ℝ := fun y => C' / δ * 2 * (dP y ^ (-(σs - 2 * δ)) + dP y ^ (-(σs + 2 * δ)))
  have hBint : Integrable B := by
    refine ((hint _ ?_).add (hint _ ?_)).const_mul (C' / δ * 2)
    · rw [hδ]; linarith
    · rw [hδ]; linarith
  have hbound : ∀ y, ∀ z ∈ Metric.ball z0 δ, ‖F' z y‖ ≤ B y := by
    intro y z hz
    have hp := dP_pos hI y
    have hre : |z.re - z0.re| < δ := by
      have := Complex.abs_re_le_norm (z - z0)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    have hn : ‖F' z y‖ = dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖ := by
      simp only [F', norm_mul, norm_neg, norm_chr, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
    rw [hn]
    have e1 := abs_log_le (dP y) δ hp hδpos
    have e2 := hb' y
    have q1 : dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ - δ)) := by
      rw [rp3 hp]; congr 1; ring
    have q2 : dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ + δ)) := by
      rw [rp3 hp]; congr 1; ring
    have r1 := rpow_neg_le_add (dP y) (z.re + κ - δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have r2 := rpow_neg_le_add (dP y) (z.re + κ + δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have a0 := Real.rpow_nonneg hp.le (-z.re)
    have a1 := Real.rpow_nonneg hp.le δ
    have a2 := Real.rpow_nonneg hp.le (-δ)
    have a3 := Real.rpow_nonneg hp.le (-κ)
    calc dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖
        ≤ dP y ^ (-z.re) * ((dP y ^ δ + dP y ^ (-δ)) / δ) * (C' * dP y ^ (-κ)) := by
          gcongr
      _ = C' / δ * (dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) + dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ)) := by
          ring
      _ = C' / δ * (dP y ^ (-(z.re + κ - δ)) + dP y ^ (-(z.re + κ + δ))) := by rw [q1, q2]
      _ ≤ B y := by
          have : 0 ≤ C' / δ := div_nonneg hC'0 hδpos.le
          simp only [B]
          nlinarith
  have hdiff : ∀ y, ∀ z ∈ Metric.ball z0 δ, HasDerivAt (fun w => F w y) (F' z y) z := by
    intro y z _
    have hp := dP_pos hI y
    have hx : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have h1 : HasDerivAt (fun w : ℂ => ((dP y : ℝ) : ℂ) ^ (-w))
        (((dP y : ℝ) : ℂ) ^ (-z) * Complex.log ((dP y : ℝ) : ℂ) * (-1)) z :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hx)).hasDerivAt).comp z (hasDerivAt_neg z)
    have h2 := (h1.mul_const (h y)).mul_const (chr t β y)
    refine h2.congr_deriv ?_
    show _ = ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
    rw [Complex.ofReal_log hp.le]
    ring
  have hF0 : Integrable (F z0) := integ_term hI t β hh hb' hz0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (x₀ := z0)
    (Metric.ball_mem_nhds z0 hδpos)
    (Eventually.of_forall fun z => (continuous_term hI t β hh z).aestronglyMeasurable) hF0
    hF'c.aestronglyMeasurable (ae_of_all _ hbound) hBint (ae_of_all _ hdiff)
  exact key.2.differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.WR.T
