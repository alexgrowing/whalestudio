import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open Filter Metric Set
open scoped Topology

namespace GlobalTheory

theorem exists_circle_ne_zero_of_frequently_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨z₁, hz₁, hz₁b⟩ := (hfr.and_eventually (ball_mem_nhds z₀ (half_pos hε))).exists
  have hv : ‖z₁ - z₀‖ < ε / 2 := by simpa [dist_eq_norm] using hz₁b
  have hmem : ∀ t ∈ ball (0 : ℂ) 2, z₀ + t • (z₁ - z₀) ∈ S := by
    intro t ht
    apply hεS
    rw [mem_ball_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (z₁ - z₀)]
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (z₀ + t • (z₁ - z₀))) (ball 0 2) :=
    hg.comp (f := fun t : ℂ => z₀ + t • (z₁ - z₀)) (by fun_prop) hmem
  have han := hd.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  rcases (han 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 2).isPreconnected
      h0 h (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact absurd (by simpa using this) hz₁
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1
      (h.and (ball_mem_nhds (0 : ℂ) two_pos))
    refine ⟨z₁ - z₀, r, hr, fun t ht => hmem t (hrs ht).2, fun t ht => ?_⟩
    refine (hrs (sphere_subset_closedBall ht)).1 ?_
    rintro rfl
    simp at ht
    exact hr.ne ht

theorem differentiableOn_quotient_of_differentiableOn_slice :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by
  intro V V' _ _ _ _ _ _ W f θ F hW hf hθ hF hsl hfr w hw
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) (hfr w hw)
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · have hEq : ∀ y ∈ U, F y = (2 * Real.pi)⁻¹ • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)) := by
      intro y hy
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (p y t)) (closedBall 0 r) :=
        (hsl y.1).comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (p y t)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def] at hav
      have : F y = F (p y 0) := by simp [p]
      rw [this, ← hav]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      rw [eq_div_iff ((hU y hy).2 _ hs), hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))]
    have hFU : DifferentiableOn ℂ F U := (hG.const_smul ((2 * Real.pi)⁻¹ : ℝ)).congr hEq
    exact (hFU.differentiableAt (hUo.mem_nhds hwU)).differentiableWithinAt
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

end GlobalTheory
