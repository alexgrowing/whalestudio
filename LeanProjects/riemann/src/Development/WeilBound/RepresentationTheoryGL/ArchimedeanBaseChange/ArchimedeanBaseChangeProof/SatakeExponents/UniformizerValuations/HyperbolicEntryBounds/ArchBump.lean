import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem cosh_im_zero (c : ℂ) (hc : c.im = 0) (t : ℝ) : (Complex.cosh (t * c ^ (1 / 2 : ℂ))).im = 0 := by
  set s := c ^ (1 / 2 : ℂ) with hs
  have hsq : s ^ 2 = c := by
    have := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
    simpa [hs, one_div] using this
  have him : s.re * s.im = 0 := by
    have h := congrArg Complex.im hsq
    rw [hc, pow_two, Complex.mul_im] at h
    linarith
  rcases mul_eq_zero.1 him with h | h
  · have e : (t : ℂ) * s = ((t * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [h]
    rw [e, Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.ofReal_im]
  · have e : (t : ℂ) * s = ((t * s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [e, ← Complex.ofReal_cosh, Complex.ofReal_im]

theorem bump_one' (ι : Type) [Fintype ι] (c : ι → ℂ) (hc : ∀ i, (c i).im = 0) :
    ∃ (g : ℝ → ℝ) (T : ℝ), 0 ≤ T ∧ IsBump g T ∧ ∏ i, coshT g (c i) = 1 := by
  have hev : ∀ᶠ t : ℝ in nhds 0, ∀ i, ‖Complex.cosh (t * c i ^ (1 / 2 : ℂ)) - 1‖ < 1 / 2 := by
    rw [Filter.eventually_all]
    intro i
    have hcont : Continuous fun t : ℝ => Complex.cosh (t * c i ^ (1 / 2 : ℂ)) := by fun_prop
    have h0 : Complex.cosh (((0 : ℝ) : ℂ) * c i ^ (1 / 2 : ℂ)) = 1 := by simp
    have ht := hcont.tendsto 0
    rw [h0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 1 (by norm_num : (0 : ℝ) < 1 / 2))).mono fun t h => by
      simpa [dist_eq_norm] using h
  obtain ⟨δ, hδ, hδt⟩ := Metric.eventually_nhds_iff.1 hev
  let f : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let g0 : ℝ → ℝ := f.normed volume
  have hnn : ∀ t, 0 ≤ g0 t := fun t => f.nonneg_normed t
  have hsupp : ∀ t, g0 t ≠ 0 → |t| < δ / 2 := by
    intro t ht
    have : t ∈ Function.support g0 := ht
    rw [show Function.support g0 = Metric.ball 0 (δ / 2) from f.support_normed_eq] at this
    simpa [Real.dist_eq] using this
  have hcr : ∀ i, Continuous fun t : ℝ => (Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re := by
    intro i; fun_prop
  let r : ι → ℝ := fun i => ∫ t, g0 t * (Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re
  have hA : ∀ i, coshT g0 (c i) = (r i : ℂ) := by
    intro i
    simp only [coshT, r]
    rw [← integral_complex_ofReal]
    congr 1
    ext t
    have e : Complex.cosh (t * c i ^ (1 / 2 : ℂ)) = ((Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re : ℂ) :=
      Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact cosh_im_zero (c i) (hc i) t)
    conv_lhs => rw [e]
    push_cast
    ring
  have hr : ∀ i, 0 < r i := by
    intro i
    have hint : Integrable (fun t => g0 t * (Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re) volume :=
      (f.continuous_normed.mul (hcr i)).integrable_of_hasCompactSupport f.hasCompactSupport_normed.mul_right
    have hle : (fun t => g0 t * (1 / 2 : ℝ)) ≤ fun t => g0 t * (Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re := by
      intro t
      by_cases h0 : g0 t = 0
      · simp [h0]
      · have ht := hsupp t h0
        have hn := hδt (show dist t 0 < δ by rw [Real.dist_eq, sub_zero]; linarith) i
        have hre : 1 / 2 ≤ (Complex.cosh (t * c i ^ (1 / 2 : ℂ))).re := by
          have h2 : |(Complex.cosh (t * c i ^ (1 / 2 : ℂ)) - 1).re| ≤ 1 / 2 := by
            have := Complex.abs_re_le_norm (Complex.cosh (t * c i ^ (1 / 2 : ℂ)) - 1)
            linarith
          rw [Complex.sub_re, Complex.one_re] at h2
          have := (abs_le.1 h2).1
          linarith
        exact mul_le_mul_of_nonneg_left hre (hnn t)
    have := integral_mono (f.integrable_normed.mul_const _) hint hle
    rw [integral_mul_const, f.integral_normed] at this
    simp only [r]
    linarith
  set P : ℝ := ∏ i, r i with hP
  have hP0 : 0 < P := Finset.prod_pos fun i _ => hr i
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨g0, δ / 2, by positivity, ⟨f.contDiff_normed, fun t => f.normed_neg t, fun t ht => ?_⟩, by simp⟩
    by_contra h
    have := hsupp t h
    linarith
  · set m : ℕ := Fintype.card ι with hm
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 0 < m := Fintype.card_pos
      exact_mod_cast this.ne'
    set l : ℝ := P ^ (-(1 : ℝ) / m) with hl
    refine ⟨fun t => l * g0 t, δ / 2, by positivity,
      ⟨contDiff_const.mul f.contDiff_normed, fun t => by simp [g0, f.normed_neg], fun t ht => ?_⟩, ?_⟩
    · have : g0 t = 0 := by
        by_contra h
        have := hsupp t h
        linarith
      simp [this]
    · have hs : ∀ i, coshT (fun t => l * g0 t) (c i) = (l : ℂ) * (r i : ℂ) := by
        intro i
        rw [← hA i]
        simp only [coshT]
        rw [← integral_const_mul]
        congr 1
        ext t
        push_cast
        ring
      simp only [hs]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hm]
      have hl' : l ^ m * P = 1 := by
        rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, div_mul_cancel₀ _ hm0, Real.rpow_neg_one,
          inv_mul_cancel₀ hP0.ne']
      have : ((l ^ m * P : ℝ) : ℂ) = 1 := by rw [hl']; simp
      rw [← this, hP]
      push_cast
      ring

end PositivityTheory.Rg.BcB.F.F0

end
