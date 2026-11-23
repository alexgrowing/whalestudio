import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory

theorem norm_root_monic_le (n : ℕ) (s : Fin n → ℂ) (y : ℂ)
    (hy : y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0) : ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖y‖ ≤ 1
  · linarith
  push_neg at h1
  cases n with
  | zero => simp at hy
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hy
    have hle : ‖y‖ ^ (m + 1) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      calc ‖y‖ ^ (m + 1) = ‖y ^ (m + 1)‖ := (norm_pow _ _).symm
        _ = ‖∑ j, s j * y ^ (j : ℕ)‖ := by rw [hyn, norm_neg]
        _ ≤ ∑ j, ‖s j * y ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ m := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          gcongr
          · exact h1.le
          · exact Nat.lt_succ_iff.1 j.isLt
        _ = (∑ j, ‖s j‖) * ‖y‖ ^ m := by rw [Finset.sum_mul]
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) _
    rw [pow_succ] at hle
    have : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith
    linarith

end GlobalTheory

namespace GlobalTheory

theorem quotient_integral_holomorphic : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  intro U n A D s hU hUc hA hD hs ⟨z₁, hz₁U, hz₁⟩ heq
  classical
  have hiso : ∀ z₀ ∈ U, ∀ᶠ w in 𝓝[≠] z₀, D w ≠ 0 := by
    intro z₀ hz₀
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    have := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hcon
    exact hz₁ (this hz₁U)
  have hroot : ∀ w ∈ U, D w ≠ 0 → (A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ) = 0 := by
    intro w hw hDw
    have hDn : D w ^ n ≠ 0 := pow_ne_zero _ hDw
    have key : D w ^ n * ((A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ))
        = A w ^ n + ∑ j, s j w * A w ^ (j : ℕ) * D w ^ (n - j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [div_pow, mul_div_cancel₀ _ hDn]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) ≤ n := j.isLt.le
        have hsplit : D w ^ n = D w ^ (j : ℕ) * D w ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
        rw [hsplit, div_pow]
        field_simp
    have := heq w hw
    rw [← key] at this
    exact (mul_eq_zero.1 this).resolve_left hDn
  have hAz : ∀ w ∈ U, D w = 0 → A w = 0 := by
    intro w hw hDw
    have := heq w hw
    have hsum : ∑ j : Fin n, s j w * A w ^ (j : ℕ) * D w ^ (n - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      rw [hDw, zero_pow (by omega : n - (j : ℕ) ≠ 0), mul_zero]
    rw [hsum, add_zero] at this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at this
    · exact (pow_eq_zero_iff hn.ne').1 this
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, ∀ z, h z =
      if D z = 0 then limUnder (𝓝[≠] z) (fun w => A w / D w) else A z / D z := ⟨_, fun z => rfl⟩
  have hdiffAt : ∀ z₀ ∈ U, DifferentiableAt ℂ h z₀ := by
    intro z₀ hz₀
    have hUn : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
    by_cases hDz : D z₀ = 0
    · have h1 : ∀ᶠ w in 𝓝 z₀, w ∈ U := hUn
      have h2 : ∀ᶠ w in 𝓝 z₀, w ≠ z₀ → D w ≠ 0 := eventually_nhdsWithin_iff.1 (hiso z₀ hz₀)
      have h3 : ∀ᶠ w in 𝓝 z₀, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := by
        rw [Filter.eventually_all]
        intro j
        have hc : ContinuousAt (fun w => ‖s j w‖) z₀ :=
          ((hs j).differentiableAt hUn).continuousAt.norm
        exact hc.eventually (Iio_mem_nhds (lt_add_one _))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
      have hsub : ∀ w ∈ Metric.ball z₀ r, w ∈ U := fun w hw => (hball w hw).1
      have hne : ∀ w ∈ Metric.ball z₀ r, w ≠ z₀ → D w ≠ 0 := fun w hw => (hball w hw).2.1
      have hsb : ∀ w ∈ Metric.ball z₀ r, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := fun w hw => (hball w hw).2.2
      have hfd : DifferentiableOn ℂ (fun w => A w / D w) (Metric.ball z₀ r \ {z₀}) := by
        intro w hw
        have hwU : U ∈ 𝓝 w := hU.mem_nhds (hsub w hw.1)
        exact ((hA.differentiableAt hwU).div (hD.differentiableAt hwU)
          (hne w hw.1 hw.2)).differentiableWithinAt
      have hbd : BddAbove (norm ∘ (fun w => A w / D w) '' (Metric.ball z₀ r \ {z₀})) := by
        refine ⟨1 + ∑ j, (‖s j z₀‖ + 1), ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have := GlobalTheory.norm_root_monic_le n (fun j => s j w) (A w / D w) (hroot w (hsub w hw.1) (hne w hw.1 hw.2))
        show ‖A w / D w‖ ≤ _
        refine this.trans ?_
        gcongr with j
        exact (hsb w hw.1 j).le
      have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds z₀ hr) hfd hbd
      have heqg : h =ᶠ[𝓝 z₀] Function.update (fun w => A w / D w) z₀
          (limUnder (𝓝[≠] z₀) (fun w => A w / D w)) := by
        filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
        by_cases hw0 : w = z₀
        · subst hw0; rw [hh, if_pos hDz, Function.update_self]
        · rw [hh, if_neg (hne w hw hw0), Function.update_of_ne hw0]
      exact (hg.differentiableAt (Metric.ball_mem_nhds z₀ hr)).congr_of_eventuallyEq heqg
    · have hDc : ContinuousAt D z₀ := (hD.differentiableAt hUn).continuousAt
      have heqf : h =ᶠ[𝓝 z₀] fun w => A w / D w := by
        filter_upwards [hDc.eventually_ne hDz] with w hw
        rw [hh, if_neg hw]
      exact ((hA.differentiableAt hUn).div (hD.differentiableAt hUn) hDz).congr_of_eventuallyEq heqf
  refine ⟨h, fun z hz => (hdiffAt z hz).differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    by_cases hDz : D z = 0
    · rw [hDz, mul_zero]; exact hAz z hz hDz
    · rw [hh, if_neg hDz, div_mul_cancel₀ _ hDz]
  · intro z hz
    by_cases hDz : D z = 0
    · have hUn : U ∈ 𝓝 z := hU.mem_nhds hz
      have hFd : DifferentiableAt ℂ (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) z := by
        apply ((hdiffAt z hz).pow n).add
        have hsum := DifferentiableAt.sum (u := Finset.univ)
          (A := fun (j : Fin n) (w : ℂ) => s j w * h w ^ (j : ℕ))
          (fun j _ => ((hs j).differentiableAt hUn).mul ((hdiffAt z hz).pow _))
        convert hsum using 1
        ext w
        simp [Finset.sum_apply]
      have hev : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ j, s j w * h w ^ (j : ℕ) = 0 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds hUn] with w hw hwU
        rw [hh, if_neg hw]
        exact hroot w hwU hw
      have ht : Tendsto (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) (𝓝[≠] z) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique (hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
    · rw [hh, if_neg hDz]
      exact hroot z hz hDz

end GlobalTheory
