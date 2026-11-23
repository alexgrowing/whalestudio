import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont.Shift

open Set Metric

theorem holValueAt_of_continuousAt {h : ℂ → ℂ} (a : GlobalTheory.Cont.Continues h) {t : ℂ}
    (b : ContinuousAt (GlobalTheory.Cont.cont h) t) : GlobalTheory.Cont.HolValueAt h t (GlobalTheory.Cont.cont h t) := by
  obtain ⟨H₀, hH⟩ := a
  have ha := hH.isExtAt (mem_univ t)
  exact ha.holValueAt_iff.2 ((b.tendsto.mono_left nhdsWithin_le_nhds).congr' ha.cont_eventuallyEq)

theorem differentiable_npow_sub {c : ℝ≥0} (hc : 0 < c) (s₁ : ℂ) : Differentiable ℂ fun s => npow c (s₁ - s) :=
  (GlobalTheory.Eis.differentiable_npow hc).comp (differentiable_const _ |>.sub differentiable_id)

theorem contMod_shift (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ) (hc : 0 < c)
    (he : ∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) (hm : ContMod T e) : ContMod T e' := by
  have hd := differentiable_npow_sub hc s₁
  have hfun : ∀ g, (fun z => e' z g) = fun z => npow c (s₁ - z) * (fun w => e w (g * x)) (z + s₂) :=
    fun g => funext fun z => he z g
  refine ⟨fun g => ?_, fun s₀ => ?_⟩
  · obtain ⟨H₀, hH⟩ := hm.1 (g * x)
    rw [GlobalTheory.Cont.isMerExt_univ] at hH
    obtain ⟨σ, hσ⟩ := hH.2
    refine ⟨fun z => npow c (s₁ - z) * H₀ (z + s₂), GlobalTheory.Cont.isMerExt_univ.2 ⟨fun z => ?_, σ - s₂.re, fun z hz => ?_⟩⟩
    · exact (hd.analyticAt z).meromorphicAt.fun_mul
        ((hH.1 (z + s₂)).comp_analyticAt (g := (· + s₂)) (by fun_prop))
    · simp only [he]
      congr 1
      exact hσ (by simpa [GlobalTheory.Cont.mem_rightOf] using sub_lt_iff_lt_add.1 hz)
  · obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hm.2 (s₀ + s₂)
    have hball : ∀ s ∈ ball s₀ r, s + s₂ ∈ ball (s₀ + s₂) r := fun s hs => by
      simpa [mem_ball, dist_eq_norm] using hs

    have hval : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g,
        GlobalTheory.Cont.cont (fun z => e' z g) s = npow c (s₁ - s) * GlobalTheory.Cont.cont (fun z => e z (g * x)) (s + s₂) := by
      intro s hs hne g
      have hne' : s + s₂ ≠ s₀ + s₂ := fun h => hne (add_right_cancel h)
      have hopen : ball (s₀ + s₂) r ∩ {s₀ + s₂}ᶜ ∈ 𝓝 (s + s₂) :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hball s hs, hne'⟩
      have hcont : ContinuousAt (GlobalTheory.Cont.cont fun z => e z (g * x)) (s + s₂) := by
        have hq : ContinuousAt (fun t => H t (g * x) / (t - (s₀ + s₂)) ^ k) (s + s₂) :=
          (((h2 (g * x)).continuousOn.continuousAt (isOpen_ball.mem_nhds (hball s hs)))).div
            (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hne'))
        refine hq.congr (Filter.eventually_of_mem hopen fun t ht => ?_)
        have := h1 t ht.1 ht.2 (g * x)
        show H t (g * x) / _ = _
        rw [this, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht.2))]
      have hv := holValueAt_of_continuousAt (hm.1 (g * x)) hcont
      have hn : GlobalTheory.Cont.HolValueAt (fun z => npow c (s₁ - z)) s (npow c (s₁ - s)) :=
        GlobalTheory.Cont.IsHolExt.holValueAt ⟨GlobalTheory.Cont.isRightDomain_univ, fun z _ => hd.analyticAt z, .refl _⟩ (mem_univ s)
      have hp := hn.mul hv.comp_add
      rw [hfun g]
      exact hp.valueAt.cont_eq
    obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hd.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ (mem_closedBall_self hr.le))
    refine ⟨k, r, fun s g => npow c (s₁ - s) * H (s + s₂) (g * x), hr, fun s hs hne g => ?_, fun g => ?_, ?_,
      B * |C| * GlobalTheory.Grow.height T x ^ N, N, fun s hs g => ?_⟩
    · show npow c (s₁ - s) * H (s + s₂) (g * x) = _
      rw [hval s hs hne g, h1 _ (hball s hs) (fun h => hne (add_right_cancel h)) (g * x)]
      rw [show s + s₂ - (s₀ + s₂) = s - s₀ by ring]
      ring
    · refine (hd.differentiableOn).mul ((h2 (g * x)).comp (by fun_prop) fun s hs => hball s hs)
    · refine (hd.continuous.comp continuous_fst).continuousOn.mul ?_
      exact h3.comp (f := fun p : ℂ × GA D T => (p.1 + s₂, p.2 * x)) (by fun_prop)
        fun (p : ℂ × GA D T) (hp : p ∈ ball s₀ r ×ˢ univ) => ⟨hball p.1 hp.1, mem_univ _⟩
    · have hH := h4 _ (hball s hs) (g * x)
      have hn := hB s (ball_subset_closedBall hs)
      have hg := GlobalTheory.Grow.height_mul_le T g x
      have hg0 := (GlobalTheory.Grow.height_pos T g).le
      have hx0 := (GlobalTheory.Grow.height_pos T x).le
      have hgx0 := (GlobalTheory.Grow.height_pos T (g * x)).le
      have e1 : ‖H (s + s₂) (g * x)‖ ≤ |C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N :=
        hH.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hgx0 N)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgx0 hg N) (abs_nonneg C)))
      rw [norm_mul]
      calc ‖npow c (s₁ - s)‖ * ‖H (s + s₂) (g * x)‖ ≤ B * (|C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N) :=
            mul_le_mul hn e1 (norm_nonneg _) hB0
        _ = B * |C| * GlobalTheory.Grow.height T x ^ N * GlobalTheory.Grow.height T g ^ N := by rw [mul_pow]; ring

end GlobalTheory.EisCont.Shift

end
