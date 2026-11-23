import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

namespace ReciprocityTheory.AnForm.P

open Filter Topology Polynomial Matrix
open scoped ContDiff

noncomputable section

theorem leviForm_half_log_abs_of_fderiv_eq_zero {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) (hd : fderiv ℝ f z = 0) (w : ι → ℂ) :
    levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z) := by
  have hev1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := hf.continuousAt.eventually_ne hz
  have hev2 : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 2 f x := hf.eventually (by simp)

  have hderiv : fderiv ℝ (fun x => (1 / 2) * Real.log |f x|) =ᶠ[𝓝 z]
      fun x => ((1 / 2) * (f x)⁻¹) • fderiv ℝ f x := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    have hfd : HasFDerivAt f (fderiv ℝ f x) x := (hx2.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasFDerivAt (fun y => (1 / 2 : ℝ) * Real.log (f y)) ((1 / 2 : ℝ) • (f x)⁻¹ • fderiv ℝ f x) x :=
      (hfd.log hx1).const_mul (1 / 2)
    have e : (fun y => (1 / 2 : ℝ) * Real.log |f y|) = fun y => (1 / 2 : ℝ) * Real.log (f y) := by
      funext y
      rw [Real.log_abs]
    rw [e, hl.fderiv, smul_smul]
  have hL : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfz : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun x => (1 / 2 : ℝ) * (f x)⁻¹) _ z :=
    ((hasDerivAt_inv hz).comp_hasFDerivAt z hfz).const_mul (1 / 2 : ℝ)
  have hprod := hc.smul hL
  unfold levi
  have hprod' : HasFDerivAt (fun x => ((1 / 2 : ℝ) * (f x)⁻¹) • fderiv ℝ f x) _ z := hprod
  rw [hderiv.fderiv_eq, hprod'.fderiv, hd]
  simp
  field_simp

theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    {v : E} {t : ℝ} (h : DifferentiableAt ℝ φ (t • v)) :
    HasDerivAt (fun s : ℝ => φ (s • v)) (fderiv ℝ φ (t • v) v) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by simpa using (hasDerivAt_id t).smul_const v
  exact h.hasFDerivAt.comp_hasDerivAt t h1

theorem deriv2_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (v : E) :
    deriv (deriv (fun s : ℝ => φ (s • v))) 0 = fderiv ℝ (fderiv ℝ φ) 0 v v := by
  have hd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable (by norm_num) x
  have e : deriv (fun s : ℝ => φ (s • v)) = fun s => fderiv ℝ φ (s • v) v := by
    funext s
    exact (hasDerivAt_line (hd _)).deriv
  rw [e]
  have hf2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h2 := (hf2 ((0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [zero_smul] at h3
  simpa using h3.deriv

theorem levi_eq_lines {ι : Type*} [Fintype ι] {φ : (ι → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv (fun s : ℝ => φ (s • w))) 0 +
      deriv (deriv (fun s : ℝ => φ (s • (Complex.I • w)))) 0) / 4 := by
  unfold levi
  rw [deriv2_line hφ w, deriv2_line hφ (Complex.I • w)]

theorem fderiv_line_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    (hφ : DifferentiableAt ℝ φ 0) (v : E) :
    fderiv ℝ φ 0 v = deriv (fun s : ℝ => φ (s • v)) 0 := by
  have h := hasDerivAt_line (v := v) (t := 0) (by rwa [zero_smul])
  rw [h.deriv, zero_smul]

theorem deriv_re_eval (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) = fun s : ℝ => (D.derivative.eval (s : ℂ)).re := by
  funext s
  exact ((Polynomial.hasDerivAt D (s : ℂ)).real_of_complex).deriv

theorem deriv_re_eval_zero (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) 0 = (D.coeff 1).re := by
  rw [deriv_re_eval]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]

theorem deriv2_re_eval_zero (D : ℂ[X]) :
    deriv (deriv (fun s : ℝ => (D.eval (s : ℂ)).re)) 0 = 2 * (D.coeff 2).re := by
  rw [deriv_re_eval, deriv_re_eval]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  ring

def cf {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) : Matrix α β ℂ := P.map fun p => p.coeff n

theorem cf_apply {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) (i : α) (j : β) :
    cf n P i j = (P i j).coeff n := rfl

theorem cf_mul {α β γ : Type*} [Fintype β] (n : ℕ) (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf n (P * Q) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, cf x.1 P * cf x.2 Q := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_mul,
    Matrix.sum_apply]
  exact Finset.sum_comm

theorem cf_mapC_mul {α β γ : Type*} [Fintype β] (n : ℕ) (A : Matrix α β ℂ)
    (P : Matrix β γ ℂ[X]) : cf n (A.map C * P) = A * cf n P := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]

theorem coeff_X_mul_C (a : ℂ) (n : ℕ) : (X * C a).coeff n = if n = 1 then a else 0 := by
  rw [mul_comm, Polynomial.coeff_C_mul_X]

theorem eq_X_sq_mul (q : ℂ[X]) (h0 : q.coeff 0 = 0) (h1 : q.coeff 1 = 0) :
    q = X ^ 2 * q.divX.divX := by
  have e1 := Polynomial.X_mul_divX_add q
  have e2 := Polynomial.X_mul_divX_add q.divX
  rw [h0, map_zero, add_zero] at e1
  rw [Polynomial.coeff_divX, zero_add, h1, map_zero, add_zero] at e2
  calc q = X * q.divX := e1.symm
    _ = X * (X * q.divX.divX) := by rw [e2]
    _ = X ^ 2 * q.divX.divX := by ring

theorem det_map_C_add_X_sq_smul {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (M : Matrix n n ℂ[X]) :
    ∃ r : ℂ[X], (A.map C + (X ^ 2 : ℂ[X]) • M).det = C A.det + X ^ 2 * r := by
  have hmap : (A.map C + (X ^ 2 : ℂ[X]) • M).map (Ideal.Quotient.mk (Ideal.span {X ^ 2})) =
      (A.map C).map (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) := by
    ext i j
    simp [Ideal.Quotient.mk_singleton_self]
  have h := congrArg Matrix.det hmap
  have e1 : (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C + (X ^ 2 : ℂ[X]) • M).det =
      (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e1
  obtain ⟨r, hr⟩ := e1
  refine ⟨r, ?_⟩
  have hdet : (A.map C).det = C A.det := (RingHom.map_det C A).symm
  rw [hdet] at hr
  linear_combination hr

theorem eq_map_C_add_X_sq_smul {n : Type*} (P : Matrix n n ℂ[X]) (h1 : cf 1 P = 0) :
    P = (cf 0 P).map C + (X ^ 2 : ℂ[X]) • (P - (cf 0 P).map C).map (fun q => q.divX.divX) := by
  ext i j
  have h1' : (P i j).coeff 1 = 0 := by
    have := congrFun (congrFun h1 i) j
    simpa [cf] using this
  have hq0 : (P i j - C ((P i j).coeff 0)).coeff 0 = 0 := by simp
  have hq1 : (P i j - C ((P i j).coeff 0)).coeff 1 = 0 := by simp [h1', Polynomial.coeff_C]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, cf]
  rw [← eq_X_sq_mul _ hq0 hq1]
  ring

theorem det_coeff_zero_one_of_coeffMatrix_one {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (h1 : cf 1 P = 0) : P.det.coeff 0 = (cf 0 P).det ∧ P.det.coeff 1 = 0 := by
  obtain ⟨r, hr⟩ := det_map_C_add_X_sq_smul (cf 0 P) ((P - (cf 0 P).map C).map fun q => q.divX.divX)
  rw [← eq_map_C_add_X_sq_smul P h1] at hr
  rw [hr]
  constructor
  · simp [Polynomial.coeff_X_pow_mul']
  · simp [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]

theorem coeff2_det_of {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (d : n → ℂ) (hd : ∀ a, d a ≠ 0) (h0 : cf 0 P = diagonal d) (h1 : cf 1 P = 0) :
    P.det.coeff 2 = (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 P a a := by
  set N : Matrix n n ℂ[X] := (P - (cf 0 P).map C).map (fun q => q.divX.divX) with hN
  set K : Matrix n n ℂ[X] := diagonal (fun a => C (d a)⁻¹) * N with hK
  have hP := eq_map_C_add_X_sq_smul P h1
  rw [← hN] at hP
  have hD : (cf 0 P).map C = diagonal (fun a => C (d a)) := by
    rw [h0, Matrix.diagonal_map (map_zero C)]

  have hfac : P = diagonal (fun a => C (d a)) * (1 + ((X : ℂ[X]) ^ 2) • K) := by
    have hone : diagonal (fun a => C (d a)) * diagonal (fun a => C (d a)⁻¹) = (1 : Matrix n n ℂ[X]) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← map_mul, mul_inv_cancel₀ (hd a), map_one]
    rw [mul_add, mul_one, Matrix.mul_smul, hK, ← mul_assoc, hone, one_mul, ← hD]
    exact hP
  have hdet : P.det = C (∏ a, d a) * (1 + ((X : ℂ[X]) ^ 2) • K).det := by
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, map_prod]
  rw [hdet, Polynomial.coeff_C_mul, Matrix.det_one_add_smul]
  have e4 : ((X : ℂ[X]) ^ 2) ^ 2 = X ^ 4 := by ring
  rw [e4, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_X_pow']
  simp only [show ¬ (4 ≤ 2) by norm_num, show (2 ≤ 2) by norm_num, if_false, if_true, Nat.sub_self,
    add_zero, Polynomial.coeff_one, show (2 : ℕ) ≠ 0 by norm_num, if_false, zero_add]
  congr 1
  rw [Matrix.trace, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, hK, Matrix.diagonal_mul, Polynomial.coeff_C_mul, hN]
  simp [Polynomial.coeff_divX, cf]

end

end ReciprocityTheory.AnForm.P
