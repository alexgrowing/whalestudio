import Mathlib

noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

theorem differentiable_cons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_const x
  · simp only [Fin.cons_succ]
    exact differentiable_pi.1 differentiable_id j

theorem differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · simp only [Fin.cons_succ]
    exact differentiable_const _

theorem mem_closedBall_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedBall c r ↔ ∀ i, z i ∈ closedBall (c i) r := by
  rw [closedBall_pi c hr, Set.mem_univ_pi]

theorem mem_ball_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by
  rw [ball_pi c hr, Set.mem_univ_pi]

theorem norm_torusMap_sub {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  have h : torusMap c (fun _ => r) θ i - c i = (r : ℂ) * exp ((θ i : ℂ) * I) := by
    simp only [torusMap]
    ring
  have h1 : ‖exp ((θ i : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(r : ℂ)‖ = r := by
    exact Complex.norm_of_nonneg hr
  rw [h, norm_mul, h1, h2, mul_one]

theorem torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  refine (mem_closedBall_pi_iff hr).2 fun i => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_torusMap_sub c hr θ i).le

theorem torusMap_sub_ne {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := (mem_ball_pi_iff hr).1 hz i
  rw [mem_ball, dist_eq_norm] at h1
  have h2 := norm_torusMap_sub c hr.le θ i
  rw [sub_eq_zero] at h
  rw [h] at h2
  linarith

theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by
  refine continuous_pi fun i => ?_
  simp only [torusMap]
  fun_prop

theorem continuous_comp_torusMap {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  exact (hf _ (torusMap_mem_closedBall c hr θ)).continuousAt.comp
    (continuous_torusMap c r).continuousAt

theorem torusIntegrable_kernel {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  have hK : Continuous fun θ => ∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹ := by
    refine continuous_finsetProd Finset.univ fun i _ => ?_
    refine Continuous.inv₀ ?_ ?_
    · exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    · intro θ
      exact torusMap_sub_ne hr hz θ i
  have hcont : Continuous fun θ =>
      (∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹) * f (torusMap c (fun _ => r) θ) :=
    hK.mul (continuous_comp_torusMap hr.le hf)
  unfold TorusIntegrable
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

theorem cauchy_polydisc : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    (∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel hr hf hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have ih := cauchy_polydisc n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr
        (fun ζ hζ => (hf _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ)) (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      fun x hx => ((hf _ (hcons x hx _ (ball_subset_closedBall hz'))).comp x
        (differentiable_cons_left (Fin.tail z) x)).differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end ReciprocityTheory.AnForm.Osgood
