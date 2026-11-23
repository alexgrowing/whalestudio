import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

open scoped Real

noncomputable section

namespace OsgoodSeparate

theorem cons_mem_ball {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := pos_of_mem_ball hx
  refine (mem_ball_pi_iff hR).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa [Fin.tail] using (mem_ball_pi_iff hR).mp hy j

theorem cauchy_torus : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, c, _, _, _, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, G, c, R, hc, hs, r, hr0, hrR, z, hz => by
    have htor : ∀ θ, torusMap c (fun _ => r) θ ∈ ball c R := fun θ =>
      closedBall_subset_ball hrR (torusMap_mem_closedBall c hr0.le θ)
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) c (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (hc.comp_continuous (continuous_torusMap c r) htor)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    rw [torusIntegral_succ hint]
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'R : Fin.tail z ∈ ball (Fin.tail c) R := ball_subset_ball hrR.le hz'
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr0).mp hz 0
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere (c 0) r) := by
      intro x hx
      have hxR : x ∈ ball (c 0) R := mem_ball.mpr (by rw [mem_sphere.mp hx]; exact hrR)
      have hc' : ContinuousOn (fun y => G (Fin.cons x y)) (ball (Fin.tail c) R) :=
        hc.comp (differentiable_cons_right x).continuous.continuousOn fun y hy => cons_mem_ball hxR hy
      have hs' : ∀ w ∈ ball (Fin.tail c) R, ∀ i : Fin n,
          DifferentiableAt ℂ (fun t => (fun y => G (Fin.cons x y)) (Function.update w i t)) (w i) := by
        intro w hw i
        have h := hs _ (cons_mem_ball hxR hw) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      have ih := cauchy_torus n (fun y => G (Fin.cons x y)) (Fin.tail c) R hc' hs' r hr0 hrR
        (Fin.tail z) hz'
      have e0 : c ∘ Fin.succ = Fin.tail c := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    have hcont : ContinuousOn (fun x => G (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      hc.comp (differentiable_cons_left (Fin.tail z)).continuous.continuousOn fun x hx =>
        cons_mem_ball (closedBall_subset_ball hrR hx) hz'R
    have hdiff : ∀ x ∈ ball (c 0) r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x := by
      intro x hx
      have h := hs _ (cons_mem_ball (ball_subset_ball hrR.le hx.1) hz'R) 0
      simp only [Fin.cons_zero, Fin.update_cons_zero] at h
      exact h
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end OsgoodSeparate

open OsgoodSeparate in

theorem analyticOnNhd_of_continuousOn_of_separately {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    AnalyticOnNhd ℂ g U := by
  intro c hcU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcb : ContinuousOn g (ball c ε) := hc.mono hball
  have hsb : ∀ z ∈ ball c ε, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i) :=
    fun z hz => hs z (hball hz)
  have htor : Continuous fun θ => g (torusMap c (fun _ => ε / 2) θ) :=
    hcb.comp_continuous (continuous_torusMap c _) fun θ =>
      closedBall_subset_ball hrε (torusMap_mem_closedBall c hr.le θ)
  set L := torusFunctional c (ε / 2) g htor
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern c (ε / 2) z)) c :=
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem c hr (mem_ball_self hr)))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl c (ε / 2) g (kern c (ε / 2) z) = g z
  rw [fctl_kern hr g hz, cauchy_torus n g c ε hcb hsb (ε / 2) hr hrε z hz, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

theorem differentiableOn_of_continuousOn_of_separately {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    DifferentiableOn ℂ g U :=
  (analyticOnNhd_of_continuousOn_of_separately hU hc hs).differentiableOn

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
