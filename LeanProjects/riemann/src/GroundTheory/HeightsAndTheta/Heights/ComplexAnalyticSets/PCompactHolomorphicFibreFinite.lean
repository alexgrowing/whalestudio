import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompactHolomorphicFibreFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNonIsolatedFibreCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace CompactHolomorphicFibreFinite

theorem sum_normSq_sub {k : ℕ} (v p : Fin k → ℂ) :
    ∑ i, Complex.normSq (v i - p i) =
      ∑ i, Complex.normSq (v i) + ∑ i, Complex.normSq (p i) -
        2 * (∑ i, v i * (starRingEnd ℂ) (p i)).re := by
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_sub]

theorem proof (hCurve : NonIsolatedFibreCurve.Statement) : CompactHolomorphicFibreFinite.Statement := by
  intro k m U f y hU hf hZ
  set Z := {v | v ∈ U ∧ f v = y} with hZdef
  by_contra hinf
  have hD : derivedSet Z ⊆ Z := (isClosed_iff_derivedSet_subset Z).1 hZ.isClosed
  have hDc : IsCompact (derivedSet Z) := hZ.of_isClosed_subset (isClosed_derivedSet Z) hD
  obtain ⟨a, -, ha⟩ := hZ.isCountablyCompact.exists_accPt_of_infinite subset_rfl hinf
  let φ : (Fin k → ℂ) → ℝ := fun v => ∑ i, Complex.normSq (v i)
  have hφc : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact Complex.continuous_normSq.comp (continuous_apply i)
  obtain ⟨p, hpD, hpmax⟩ := hDc.exists_isMaxOn ⟨a, ha⟩ hφc.continuousOn
  have hpZ : p ∈ Z := hD hpD
  have hZeq : {v | v ∈ U ∧ f v = f p} = Z := by rw [hpZ.2]
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγZ⟩ :=
    hCurve k m U f p hU hf hpZ.1 (by rw [hZeq]; exact hpD)
  rw [hZeq] at hγZ

  have hγD : ∀ τ ∈ ball (0 : ℂ) r, γ τ ∈ derivedSet Z := by
    intro τ hτ
    rw [mem_derivedSet, accPt_iff_nhds]
    intro N hN
    have hτn : ball (0 : ℂ) r ∈ 𝓝 τ := isOpen_ball.mem_nhds hτ
    have hcont : ContinuousAt γ τ := hγd.continuousOn.continuousAt hτn
    have hev : ∀ᶠ s in 𝓝[≠] τ, (s ∈ ball (0 : ℂ) r ∧ γ s ∈ N) ∧ s ≠ τ :=
      (((show ∀ᶠ s in 𝓝 τ, s ∈ ball (0 : ℂ) r from hτn).and
        (show ∀ᶠ s in 𝓝 τ, γ s ∈ N from hcont hN)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨s, ⟨hs, hsN⟩, hne⟩ := hev.exists
    exact ⟨γ s, ⟨hsN, hγZ hs⟩, fun h => hne (hγi hs hτ h)⟩
  let h : ℂ → ℂ := fun τ => ∑ i, γ τ i * (starRingEnd ℂ) (p i)
  have hhd : DifferentiableOn ℂ h (ball 0 r) := by
    intro τ hτ
    refine DifferentiableWithinAt.fun_sum fun i _ => ?_
    exact (differentiableWithinAt_pi.1 (hγd τ hτ) i).mul_const _
  have hexp : ∀ τ, ∑ i, Complex.normSq (γ τ i - p i) = φ (γ τ) + φ p - 2 * (h τ).re :=
    fun τ => sum_normSq_sub (γ τ) p
  have hnn : ∀ τ, 0 ≤ ∑ i, Complex.normSq (γ τ i - p i) :=
    fun τ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hh0 : (h 0).re = φ p := by
    have e := hexp 0
    simp only [hγ0, sub_self, map_zero, Finset.sum_const_zero] at e
    linarith
  have hle : ∀ τ ∈ ball (0 : ℂ) r, (h τ).re ≤ φ p := by
    intro τ hτ
    have h1 : φ (γ τ) ≤ φ p := hpmax (hγD τ hτ)
    have h2 := hexp τ
    have h3 := hnn τ
    linarith
  have hmax : IsMaxOn (norm ∘ fun τ => Complex.exp (h τ)) (ball 0 r) 0 := by
    intro τ hτ
    simp only [Function.comp_apply, Complex.norm_exp]
    rw [hh0]
    exact Real.exp_le_exp.2 (hle τ hτ)
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) r).isPreconnected
    isOpen_ball hhd.cexp (mem_ball_self hr) hmax
  have hτ : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hre : (h ((r / 2 : ℝ) : ℂ)).re = φ p := by
    have e := congrArg (fun z : ℂ => ‖z‖) (hconst hτ)
    simp only [Function.const_apply, Complex.norm_exp] at e
    rw [← hh0]
    exact Real.exp_injective e
  have hzero : ∑ i, Complex.normSq (γ ((r / 2 : ℝ) : ℂ) i - p i) = 0 := by
    have h1 : φ (γ ((r / 2 : ℝ) : ℂ)) ≤ φ p := hpmax (hγD _ hτ)
    have h2 := hexp ((r / 2 : ℝ) : ℂ)
    have h3 := hnn ((r / 2 : ℝ) : ℂ)
    linarith
  have hγp : γ ((r / 2 : ℝ) : ℂ) = γ 0 := by
    rw [hγ0]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 hzero i
      (Finset.mem_univ i)
    exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 hi)
  have h0 := hγi hτ (mem_ball_self hr) hγp
  simp only [Complex.ofReal_eq_zero] at h0
  exact (half_pos hr).ne' h0

end CompactHolomorphicFibreFinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
