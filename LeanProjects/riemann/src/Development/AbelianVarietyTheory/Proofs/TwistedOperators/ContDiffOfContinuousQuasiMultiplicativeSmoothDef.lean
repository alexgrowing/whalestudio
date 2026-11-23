import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory

open Metric Set Filter Topology Convolution

namespace GlobalTheory.FuncEqSmooth

theorem contDiff_of_func_eq (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hc : Continuous c)
    (hc0 : c 0 ≠ 0) (hU : IsOpen U) (hUs : ∀ s, (s, 0) ∈ U)
    (hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U)
    (hfe : ∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  have h00 : ((0:ℝ), (0:ℝ)) ∈ U := hUs 0
  have hw0 : c 0 * E 0 0 = 1 := by
    have h1 := hfe (0,0) h00
    simp only [add_zero] at h1
    have h2 : c 0 * (c 0 * E 0 0) = c 0 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel₀ hc0 h2
  have hEcont : ContinuousAt (fun p : ℝ × ℝ => E p.1 p.2) (0,0) :=
    hE.continuousOn.continuousAt (hU.mem_nhds h00)
  have hwcont : ContinuousAt (fun v : ℝ => c v * E 0 v) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => E (0:ℝ) v) 0 :=
      hEcont.comp (f := fun v : ℝ => ((0:ℝ), v)) (by fun_prop)
    exact hc.continuousAt.mul h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ h00
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.1 hwcont (1/2) (by norm_num)
  set r := min ε δ with hr
  have hr0 : 0 < r := lt_min hε hδ
  have hbox : ∀ a b : ℝ, |a| < r → |b| < r → (a, b) ∈ U := by
    intro a b ha hb
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero]
    exact ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_lt_of_le hb (min_le_left _ _)⟩

  let ψ : ContDiffBump (0:ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
  set φ : ℝ → ℝ := ψ.normed volume with hφdef
  have hφ0 : ∀ x : ℝ, r/2 ≤ |x| → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support, hφdef, ψ.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    show ¬ |x| < r/2
    linarith
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := ψ.contDiff_normed
  let φr : ℝ → ℂ := fun y => ((φ y : ℝ) : ℂ)
  have hφr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φr := Complex.ofRealCLM.contDiff.comp hφs
  have hφr0 : ∀ x : ℝ, r/2 ≤ |x| → φr x = 0 := by
    intro x hx; simp [φr, hφ0 x hx]

  let A : ℝ → ℂ := c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have hcs : HasCompactSupport (fun y => φr (-y)) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (r/2)) (fun y hy => ?_)
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
      exact hφr0 _ (by rw [abs_neg]; exact hy.le)
    exact hcs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ) hc.locallyIntegrable
      (hφr.comp contDiff_neg)

  let G : ℝ → ℝ → ℂ := fun t y => φr (-y) * E t (-y)
  let h : ℝ → ℂ := fun t => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) (ball (0:ℝ) r ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hq1 : |q.1| < r := by
      have := hq.1; rw [mem_ball, Real.dist_eq, sub_zero] at this; exact this
    by_cases hq2 : |q.2| < r
    · have hmem : (q.1, -q.2) ∈ U := hbox _ _ hq1 (by rw [abs_neg]; exact hq2)
      have hEat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) (q.1, -q.2) :=
        hE.contDiffAt (hU.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => E q.1 (-q.2)) q :=
        hEat.comp (f := fun q : ℝ × ℝ => (q.1, -q.2)) q (by fun_prop)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => φr (-q.2)) q :=
        (hφr.comp (contDiff_snd.neg)).contDiffAt
      exact h1.mul h2
    · push_neg at hq2
      have hev : ∀ᶠ q' in 𝓝 q, r/2 < |q'.2| :=
        continuousAt_const.eventually_lt (by fun_prop) (by linarith)
      refine contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q' hq'
      show φr (-q'.2) * E q'.1 (-q'.2) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hq'.le), zero_mul]
  have hparam := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (f := c) (g := G) (s := ball (0:ℝ) r) (k := closedBall (0:ℝ) (r/2))
    isOpen_ball (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      show φr (-x) * E p (-x) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hx.le), zero_mul])
    hc.locallyIntegrable hG
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0:ℝ) r) := by
    have hemb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t, (0:ℝ))) (ball (0:ℝ) r) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have h3 := ContDiffOn.comp (g := fun q : ℝ × ℝ => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G q.1) q.2)
      hparam hemb (fun t ht => ⟨ht, mem_univ _⟩)
    exact h3
  have hrδ : r ≤ δ := min_le_right _ _

  let cl : ℝ → ℝ := fun v => max (-(r/2)) (min v (r/2))
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl : ∀ v, cl v ∈ Icc (-(r/2)) (r/2) := fun v =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclid : ∀ v, |v| ≤ r/2 → cl v = v := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    show max (-(r/2)) (min v (r/2)) = v
    rw [min_eq_left h2, max_eq_right h1]
  have hE0on : ContinuousOn (fun v : ℝ => E 0 v) (Icc (-(r/2)) (r/2)) := by
    have h3 := hE.continuousOn.comp (f := fun v : ℝ => ((0:ℝ), v))
      (by fun_prop : Continuous fun v : ℝ => ((0:ℝ), v)).continuousOn
      (fun v (hv : v ∈ Icc (-(r/2)) (r/2)) => hbox 0 v (by simp [hr0]) (abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩))
    exact h3
  let Ehat : ℝ → ℂ := fun v => E 0 (cl v)
  have hEhat : Continuous Ehat := hE0on.comp_continuous hclc hcl
  let g : ℝ → ℂ := fun x => c (-x) * Ehat (-x)
  have hgc : Continuous g := (hc.comp continuous_neg).mul (hEhat.comp continuous_neg)
  have hg0 : g 0 = 1 := by
    show c (-0) * E 0 (cl (-0)) = 1
    rw [neg_zero, hclid 0 (by simp; positivity), hw0]
  have hdist := ψ.dist_normed_convolution_le (μ := volume) (x₀ := 0) (ε := 1/2) hgc.aestronglyMeasurable
    (fun x hx => by
      have hx' : |x| < r/2 := by
        have h6 := hx; rw [mem_ball, Real.dist_eq, sub_zero] at h6; exact h6
      have e1 : g x = c (-x) * E 0 (-x) := by
        show c (-x) * E 0 (cl (-x)) = _
        rw [hclid _ (by rw [abs_neg]; exact hx'.le)]
      rw [e1, hg0, ← hw0]
      exact (hwδ (by rw [Real.dist_eq, sub_zero, abs_neg]; linarith)).le)
  have hconv : (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0 = h 0 := by
    show _ = (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G 0) 0
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g, G, Ehat, φr]
    by_cases hu : |u| < r/2
    · rw [hclid u hu.le, Complex.real_smul]; ring
    · have hz : ψ.normed volume u = 0 := hφ0 u (not_lt.1 hu)
      have hz' : φ u = 0 := hφ0 u (not_lt.1 hu)
      rw [hz, hz']; simp
  have h0ne : h 0 ≠ 0 := by
    intro h0
    rw [hconv, hg0, h0] at hdist
    norm_num at hdist

  have hAh : ∀ t, |t| < r → A t = c t * h t := by
    intro t ht
    show (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))) t
      = c t * (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
    rw [convolution_def, convolution_def, ← integral_const_mul,
      ← integral_add_right_eq_self (μ := volume)
        (fun u => (ContinuousLinearMap.mul ℝ ℂ) (c u) (φr (-(t - u)))) t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply', G, zero_sub, neg_neg]
    have e : -(t - (s + t)) = s := by ring
    rw [e]
    by_cases hs : |s| < r/2
    · have h7 := hfe (t, s) (hbox t s ht (by linarith))
      simp only at h7
      rw [add_comm s t, h7]; ring
    · rw [hφr0 s (not_lt.1 hs)]; ring

  have hcont_h : ContinuousOn h (ball (0:ℝ) r) := hh.continuousOn
  set V := ball (0:ℝ) r ∩ h ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := hcont_h.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have h0V : (0:ℝ) ∈ V := ⟨mem_ball_self hr0, h0ne⟩
  have hcV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c V := by
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t * (h t)⁻¹) V :=
      hA.contDiffOn.mul ((hh.mono inter_subset_left).inv (fun t ht => ht.2))
    refine h4.congr (fun t ht => ?_)
    have ht1 : |t| < r := by
      have h8 := ht.1; rw [mem_ball, Real.dist_eq, sub_zero] at h8; exact h8
    have hne : h t ≠ 0 := ht.2
    show c t = A t * (h t)⁻¹
    rw [hAh t ht1, mul_inv_cancel_right₀ hne]

  rw [contDiff_iff_contDiffAt]
  intro t₀
  set W := (fun t : ℝ => (t₀, t)) ⁻¹' U ∩ V with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter hVo
  have h0W : (0:ℝ) ∈ W := ⟨hUs t₀, h0V⟩
  have hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) W := by
    have hE' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => E t₀ t) W :=
      hE.comp (f := fun t : ℝ => (t₀, t)) (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ht.1)
    have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c t₀ * c t * E t₀ t) W :=
      (contDiffOn_const.mul (hcV.mono inter_subset_right)).mul hE'
    refine h5.congr (fun t ht => ?_)
    exact hfe (t₀, t) ht.1
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) 0 := hFW.contDiffAt (hWo.mem_nhds h0W)
  have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x - t₀) t₀ := (contDiff_id.sub contDiff_const).contDiffAt
  have hF0' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) ((fun x : ℝ => x - t₀) t₀) := by
    simpa using hF0
  have h9 := ContDiffAt.comp (f := fun x : ℝ => x - t₀) t₀ hF0' hsub
  convert h9 using 1
  funext x
  simp

end GlobalTheory.FuncEqSmooth
