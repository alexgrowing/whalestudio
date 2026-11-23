import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

noncomputable section

open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform

namespace GlobalTheory.HeckeTwo.HDecay

theorem fourier_decay_of_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n f)) (N : ℕ) :
    ∃ C : ℝ, ∀ ν : ℝ, ‖𝓕 f ν‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  have hbound : ∀ (u : ℝ → ℂ) (ν : ℝ), ‖𝓕 u ν‖ ≤ ∫ t, ‖u t‖ := by
    intro u ν
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    simp [Circle.norm_smul]
  set A := ∫ t, ‖f t‖
  set B := ∫ t, ‖iteratedDeriv N f t‖
  refine ⟨2 ^ N * (A + B / (2 * Real.pi) ^ N), fun ν => ?_⟩
  have h1 : ‖𝓕 f ν‖ ≤ A := hbound f ν
  have h2 : (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) ≤ B := by
    have := hbound (iteratedDeriv N f) ν
    rw [Real.fourier_iteratedDeriv (N := ⊤) hf (fun n _ => hi n) le_top] at this
    have e : ‖(2 * (Real.pi : ℂ) * I * (ν : ℂ)) ^ N • 𝓕 f ν‖ = (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) := by
      rw [norm_smul, norm_pow]
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        abs_of_pos Real.pi_pos, mul_one]
      ring
    rw [e] at this
    exact this
  have hx : 0 ≤ |ν| := abs_nonneg ν
  have hq : 0 ≤ ‖𝓕 f ν‖ := norm_nonneg _
  have hpi : 0 < (2 * Real.pi) ^ N := by positivity
  have h3 : |ν| ^ N * ‖𝓕 f ν‖ ≤ B / (2 * Real.pi) ^ N := by
    rw [le_div_iff₀ hpi]; linarith
  have h4 : (1 + |ν|) ^ N ≤ 2 ^ N * (1 + |ν| ^ N) := by
    rcases le_total 1 |ν| with h | h
    · calc (1 + |ν|) ^ N ≤ (2 * |ν|) ^ N := by gcongr; linarith
        _ = 2 ^ N * |ν| ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by gcongr; linarith
    · calc (1 + |ν|) ^ N ≤ (2 : ℝ) ^ N := by gcongr; linarith
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by
          have : 0 ≤ |ν| ^ N := by positivity
          nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  have hpos : 0 < (1 + |ν|) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖𝓕 f ν‖ * (1 + |ν|) ^ N ≤ ‖𝓕 f ν‖ * (2 ^ N * (1 + |ν| ^ N)) := by gcongr
    _ = 2 ^ N * (‖𝓕 f ν‖ + |ν| ^ N * ‖𝓕 f ν‖) := by ring
    _ ≤ 2 ^ N * (A + B / (2 * Real.pi) ^ N) := by gcongr

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo.HDecay

variable (σ : ℂ) (y : ℝ)

def gI (t : ℝ) : ℂ := ((t : ℂ) + (y : ℂ) * I)⁻¹

def hI (t : ℝ) : ℂ := ((t : ℂ) - (y : ℂ) * I)⁻¹

def eF (t : ℝ) : ℂ := Complex.exp (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ))

def wF (a b : ℕ) (t : ℝ) : ℂ := gI y t ^ (a + 2) * hI y t ^ b * eF σ y t

variable {y}

theorem add_I_ne (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem sub_I_ne (hy : y ≠ 0) (t : ℝ) : (t : ℂ) - (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem sq_add_sq_pos (hy : y ≠ 0) (t : ℝ) : 0 < t ^ 2 + y ^ 2 := by
  have : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  positivity

theorem hasDerivAt_gI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (gI y) (-(gI y t) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * I) 1 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((y : ℂ) * I)
  refine (h1.inv (add_I_ne hy t)).congr_deriv ?_
  simp [gI, div_eq_mul_inv, inv_pow]

theorem hasDerivAt_hI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (hI y) (-(hI y t) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) - (y : ℂ) * I) 1 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).sub_const ((y : ℂ) * I)
  refine (h1.inv (sub_I_ne hy t)).congr_deriv ?_
  simp [hI, div_eq_mul_inv, inv_pow]

theorem gI_add_hI (hy : y ≠ 0) (t : ℝ) :
    gI y t + hI y t = ((2 * t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have h1 := add_I_ne hy t
  have h2 := sub_I_ne hy t
  have h3 : ((t ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sq_add_sq_pos hy t).ne'
  have hprod : ((t : ℂ) + (y : ℂ) * I) * ((t : ℂ) - (y : ℂ) * I) = ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  unfold gI hI
  rw [inv_add_inv h1 h2, hprod]
  push_cast
  ring

theorem hasDerivAt_eF (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (eF σ y) (-σ * (gI y t + hI y t) * eF σ y t) t := by
  have hpos := sq_add_sq_pos hy t
  have hL : HasDerivAt (fun s : ℝ => Real.log (s ^ 2 + y ^ 2)) (2 * t / (t ^ 2 + y ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).add_const (y ^ 2)).log hpos.ne'
    convert this using 1
    ring
  have hc := ((hL.ofReal_comp).const_mul (-σ)).cexp
  refine hc.congr_deriv ?_
  rw [gI_add_hI hy t]
  simp only [eF]
  ring

theorem hasDerivAt_wF (hy : y ≠ 0) (a b : ℕ) (t : ℝ) :
    HasDerivAt (wF σ y a b)
      (-((a : ℂ) + 2 + σ) * wF σ y (a + 1) b t - ((b : ℂ) + σ) * wF σ y a (b + 1) t) t := by
  have hg := (hasDerivAt_gI hy t).pow (a + 2)
  have hh : HasDerivAt (fun s => hI y s ^ b) (-(b : ℂ) * hI y t ^ (b + 1)) t := by
    rcases b with _ | b
    · simpa using hasDerivAt_const t (1 : ℂ)
    · refine ((hasDerivAt_hI hy t).pow (b + 1)).congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have := (hg.mul hh).mul (hasDerivAt_eF σ hy t)
  refine this.congr_deriv ?_
  have e : a + 2 - 1 = a + 1 := by omega
  simp only [wF, e, Pi.mul_apply, Pi.pow_apply]
  push_cast
  ring

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo.HDecay

variable (σ : ℂ) (y : ℝ)

def wSpan : Submodule ℂ (ℝ → ℂ) := Submodule.span ℂ (Set.range fun p : ℕ × ℕ => wF σ y p.1 p.2)

variable {σ y}

theorem wSpan_deriv (hy : y ≠ 0) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Differentiable ℝ F ∧ deriv F ∈ wSpan σ y := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    refine ⟨fun t => (hasDerivAt_wF σ hy a b t).differentiableAt, ?_⟩
    have e : deriv (wF σ y a b) =
        (-((a : ℂ) + 2 + σ)) • wF σ y (a + 1) b - ((b : ℂ) + σ) • wF σ y a (b + 1) := by
      funext t
      rw [(hasDerivAt_wF σ hy a b t).deriv]
      simp
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a + 1, b), rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b + 1), rfl⟩))
  | zero =>
    refine ⟨differentiable_const 0, ?_⟩
    have e : deriv (0 : ℝ → ℂ) = 0 := by
      funext t
      exact deriv_const t 0
    rw [e]
    exact zero_mem _
  | add F G _ _ hF hG =>
    refine ⟨hF.1.add hG.1, ?_⟩
    have e : deriv (F + G) = deriv F + deriv G := by
      funext t
      exact deriv_add (hF.1 t) (hG.1 t)
    rw [e]
    exact add_mem hF.2 hG.2
  | smul c F _ hF =>
    refine ⟨hF.1.const_smul c, ?_⟩
    have e : deriv (c • F) = c • deriv F := by
      funext t
      exact deriv_const_smul c (hF.1 t)
    rw [e]
    exact Submodule.smul_mem _ c hF.2

theorem iteratedDeriv_mem (hy : y ≠ 0) (n : ℕ) : iteratedDeriv n (wF σ y 0 0) ∈ wSpan σ y := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact Submodule.subset_span ⟨(0, 0), rfl⟩
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (wSpan_deriv hy ih).2

theorem contDiff_wF (hy : y ≠ 0) : ContDiff ℝ ∞ (wF σ y 0 0) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => (wSpan_deriv hy (iteratedDeriv_mem hy m)).1

theorem wF_integrable (hy : y ≠ 0) (hσ : 0 < σ.re) (a b : ℕ) : Integrable (wF σ y a b) := by
  have hc : Continuous (wF σ y a b) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_wF σ hy a b t).continuousAt
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hay : 0 < |y| := abs_pos.2 hy
  set K := (1 + (y ^ 2)⁻¹) * |y|⁻¹ ^ (a + b) * Real.exp (-σ.re * Real.log (y ^ 2)) with hK
  refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hpos := sq_add_sq_pos hy t
  have hnorm : ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hnorm' : ‖(t : ℂ) - (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.normSq_add_mul_I]
    ring
  have him : |y| ≤ ‖(t : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * I)
    simpa using this
  have him' : |y| ≤ ‖(t : ℂ) - (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) - (y : ℂ) * I)
    simpa using this
  have hg1 : ‖gI y t‖ ≤ |y|⁻¹ := by
    rw [gI, norm_inv]
    exact inv_anti₀ hay him
  have hh1 : ‖hI y t‖ ≤ |y|⁻¹ := by
    rw [hI, norm_inv]
    exact inv_anti₀ hay him'
  have hg2 : ‖gI y t‖ ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by
    rw [gI, norm_inv, inv_pow, hnorm]
    have key : 1 + t ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2) := by
      rw [add_mul, one_mul, inv_mul_eq_div, add_div, div_self hy2.ne']
      have : 0 ≤ t ^ 2 / y ^ 2 := by positivity
      nlinarith
    calc (t ^ 2 + y ^ 2)⁻¹ = (1 + (y ^ 2)⁻¹) * ((1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2))⁻¹ := by
          field_simp
      _ ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by gcongr
  have hE : ‖eF σ y t‖ ≤ Real.exp (-σ.re * Real.log (y ^ 2)) := by
    rw [eF, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hre : (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ)).re = -σ.re * Real.log (t ^ 2 + y ^ 2) := by
      simp [Complex.mul_re]
    rw [hre]
    have hlog : Real.log (y ^ 2) ≤ Real.log (t ^ 2 + y ^ 2) :=
      Real.log_le_log hy2 (by nlinarith [sq_nonneg t])
    nlinarith
  calc ‖wF σ y a b t‖ = ‖gI y t‖ ^ 2 * ‖gI y t‖ ^ a * ‖hI y t‖ ^ b * ‖eF σ y t‖ := by
        simp only [wF, norm_mul, norm_pow]
        ring
    _ ≤ ((1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹) * |y|⁻¹ ^ a * |y|⁻¹ ^ b *
          Real.exp (-σ.re * Real.log (y ^ 2)) := by gcongr
    _ = K * (1 + t ^ 2)⁻¹ := by
        rw [hK]
        ring

theorem wSpan_integrable (hy : y ≠ 0) (hσ : 0 < σ.re) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Integrable F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    exact wF_integrable hy hσ a b
  | zero => exact integrable_zero _ _ _
  | add F G _ _ hF hG => exact hF.add hG
  | smul c F _ hF => exact hF.smul c

theorem phi_eq_wF (hy : y ≠ 0) (t : ℝ) : phi σ ((t : ℂ) + (y : ℂ) * I) = wF σ y 0 0 t := by
  have hz := add_I_ne hy t
  have hn : 0 < ‖(t : ℂ) + (y : ℂ) * I‖ := norm_pos_iff.2 hz
  simp only [phi, wF, gI, eF, pow_zero, mul_one, zero_add]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  congr 1
  have e : t ^ 2 + y ^ 2 = ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [e, Real.log_pow]
  push_cast
  ring

theorem hTrans_eq_fourier (hy : y ≠ 0) (ν : ℝ) : hTrans σ ν y = 𝓕 (wF σ y 0 0) ν := by
  rw [Real.fourier_real_eq_integral_exp_smul, hTrans]
  congr 1
  funext t
  rw [phi_eq_wF hy t, smul_eq_mul, mul_comm (Complex.exp _)]
  congr 2
  push_cast
  ring

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo

theorem hTrans_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  intro σ hσ y hy N
  obtain ⟨C, hC⟩ := HDecay.fourier_decay_of_iteratedDeriv (HDecay.contDiff_wF hy)
    (fun n => HDecay.wSpan_integrable hy hσ (HDecay.iteratedDeriv_mem hy n)) N
  exact ⟨C, fun ν => by rw [HDecay.hTrans_eq_fourier hy ν]; exact hC ν⟩

end GlobalTheory.HeckeTwo
