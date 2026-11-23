import Mathlib

namespace GlobalTheory

theorem gaussian_ray_of_fderiv_eq_linear_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℂ) (hf : Differentiable ℝ f) (P : V → V →ₗ[ℝ] ℂ)
    (hP : ∀ x α, fderiv ℝ f x α = P α x * f x) (x : V) (t : ℝ) :
    f (t • x) = f 0 * Complex.exp ((t : ℂ) ^ 2 / 2 * P x x) := by
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (s • x)) ((s : ℂ) * P x x * f (s • x)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have h2 := (hf (s • x)).hasFDerivAt.comp_hasDerivAt s h1
    rw [hP, map_smul, Complex.real_smul] at h2
    exact h2
  have he : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 / 2 * P x x)))
      (Complex.exp (-((s : ℂ) ^ 2 / 2 * P x x)) * (-((s : ℂ) * P x x))) s := by
    intro s
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) ^ 2 / 2 * P x x)) (-((s : ℂ) * P x x)) s := by
      have h2 := ((((h0.mul h0)).div_const 2).mul_const (P x x)).neg
      have e : (fun s : ℝ => -((s : ℂ) ^ 2 / 2 * P x x)) =
          -fun y : ℝ => ((fun s : ℝ => (s : ℂ)) * fun s : ℝ => (s : ℂ)) y / 2 * P x x := by
        ext s; simp [sq]
      rw [e]
      exact h2.congr_deriv (by ring)
    exact h1.cexp
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => f (s • x) * Complex.exp (-((s : ℂ) ^ 2 / 2 * P x x))) 0 s := by
    intro s
    exact ((hg s).mul (he s)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [zero_smul, Complex.ofReal_zero] at hc
  have hc' : f (t • x) * Complex.exp (-((t : ℂ) ^ 2 / 2 * P x x)) = f 0 := by
    simpa using hc
  rw [← hc', mul_assoc, ← Complex.exp_add]
  simp

theorem schwartz_gaussian_of_fderiv_eq_linear_mul {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ) (hf : f ≠ 0)
    (P : V → V →ₗ[ℝ] ℂ) (hP : ∀ x α, fderiv ℝ (⇑f) x α = P α x * f x) :
    ∃ (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (z : ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) ∧
      ∀ x, f x = z * Complex.exp (-(Q x x)) := by
  have ray := gaussian_ray_of_fderiv_eq_linear_mul (⇑f) f.differentiable P hP
  have h1 : ∀ x, f x = f 0 * Complex.exp (1 / 2 * P x x) := by
    intro x
    simpa using ray x 1
  have h0 : f 0 ≠ 0 := by
    intro h
    apply hf
    ext x
    rw [h1 x, h]; simp
  have hne : ∀ x, f x ≠ 0 := fun x => by
    rw [h1 x]; exact mul_ne_zero h0 (Complex.exp_ne_zero _)
  have hadd : ∀ x a b, P (a + b) x = P a x + P b x := by
    intro x a b
    apply mul_right_cancel₀ (hne x)
    rw [add_mul, ← hP, ← hP, ← hP, map_add]
  have hsmul : ∀ x (c : ℝ) a, P (c • a) x = c • P a x := by
    intro x c a
    apply mul_right_cancel₀ (hne x)
    rw [smul_mul_assoc, ← hP, ← hP, map_smul]
  let Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun x y => -(1 / 2 * P y x))
    (fun a b y => by rw [map_add]; ring)
    (fun c a y => by rw [map_smul]; simp only [Complex.real_smul]; ring)
    (fun x a b => by rw [hadd]; ring)
    (fun c x a => by rw [hsmul]; simp only [Complex.real_smul]; ring)
  have hQ : ∀ x, Q x x = -(1 / 2 * P x x) := fun x => rfl
  refine ⟨Q, f 0, ?_, fun x => by rw [hQ, neg_neg]; exact h1 x⟩
  intro x hx
  by_contra hle
  push_neg at hle
  have hre : 0 ≤ (P x x).re := by
    rw [hQ] at hle
    simp at hle
    linarith
  obtain ⟨C, -, hC⟩ := f.decay 1 0
  have hlow : ∀ t : ℝ, ‖f 0‖ ≤ ‖f (t • x)‖ := by
    intro t
    rw [ray x t, norm_mul, Complex.norm_exp]
    have : (0 : ℝ) ≤ ((t : ℂ) ^ 2 / 2 * P x x).re := by
      have e : ((t : ℂ) ^ 2 / 2 * P x x) = ((t ^ 2 / 2 : ℝ) : ℂ) * P x x := by push_cast; ring
      rw [e, Complex.re_ofReal_mul]
      positivity
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp this)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hzp : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  set t : ℝ := (C + 1) / (‖x‖ * ‖f 0‖) with ht
  have htp : 0 < t := by positivity
  have h2 := hC (t • x)
  rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg htp.le] at h2
  have h3 : t * ‖x‖ * ‖f 0‖ ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left (hlow t) (by positivity)) h2
  have h4 : t * ‖x‖ * ‖f 0‖ = C + 1 := by
    rw [ht]; field_simp
  linarith

end GlobalTheory
