import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.DerivW

def cf (i j : Fin 2) : M22 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

theorem cf_apply (i j : Fin 2) (X : M22) : cf i j X = X i j := rfl

def colL (j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cf 0 j) + Complex.I • Complex.ofRealCLM.comp (cf 1 j)

theorem colL_zero (X : M22) : colL 0 X = al X := by
  simp [colL, al, cf_apply, mul_comm]

theorem colL_one (X : M22) : colL 1 X = be X := by
  simp [colL, be, cf_apply, mul_comm]

theorem hasFDerivAt_al (h : M22) : HasFDerivAt al (colL 0) h := by
  have : al = colL 0 := funext fun X => (colL_zero X).symm
  rw [this]
  exact (colL 0).hasFDerivAt

theorem hasFDerivAt_be (h : M22) : HasFDerivAt be (colL 1) h := by
  have : be = colL 1 := funext fun X => (colL_one X).symm
  rw [this]
  exact (colL 1).hasFDerivAt

def dc (h : M22) : ℂ := (((Matrix.of h).det : ℝ) : ℂ)

def dL (h : M22) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    (h 0 0 • cf 1 1 + h 1 1 • cf 0 0 - (h 0 1 • cf 1 0 + h 1 0 • cf 0 1))

theorem dL_apply (h X : M22) : dL h X = (dd h X : ℂ) := by
  simp only [dL, dd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, cf_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  congr 1
  ring

theorem hasFDerivAt_dc (h : M22) : HasFDerivAt dc (dL h) h := by
  have e : dc = fun y : M22 => Complex.ofRealCLM
      (cf 0 0 y * cf 1 1 y - cf 0 1 y * cf 1 0 y) := by
    funext y
    simp [dc, Matrix.det_fin_two, cf_apply]
  rw [e]
  have h1 := ((cf 0 0).hasFDerivAt (x := h)).mul ((cf 1 1).hasFDerivAt (x := h))
  have h2 := ((cf 0 1).hasFDerivAt (x := h)).mul ((cf 1 0).hasFDerivAt (x := h))
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp h (h1.sub h2)
  exact h3

theorem hasFDerivAt_zpow_log {f : M22 → ℂ} {f' : M22 →L[ℝ] ℂ} {x : M22}
    (hf : HasFDerivAt f f' x) (n : ℤ) (h0 : f x ≠ 0) :
    HasFDerivAt (fun y => f y ^ n) ((f x ^ n * ((n : ℂ) / f x)) • f') x := by
  have h1 := (hasDerivAt_zpow n (f x) (Or.inl h0)).comp_hasFDerivAt x hf
  have e : (n : ℂ) * f x ^ (n - 1) = f x ^ n * ((n : ℂ) / f x) := by
    rw [zpow_sub_one₀ h0]
    field_simp
  rw [e] at h1
  exact h1

def cl (k : ℕ) (h : M22) : ℂ :=
  dc h ^ (((k - 1 : ℕ)) : ℤ) * al h ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h * al h ^ (-1 : ℤ)))

theorem weight_eq_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k h = cl k h := by
  rw [GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ]
  simp only [cl, dc, al, be, zpow_natCast, zpow_neg_one, div_eq_mul_inv]

theorem weight_eventually_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k =ᶠ[nhds h] cl k := by
  have hc : Continuous fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ).det :=
    (show Continuous (fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ)) from
      continuous_id).matrix_det
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hΔ] with y hy
  exact weight_eq_closed_form k hk y hy

theorem main_deriv (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X := by
  have hA0 : al h ≠ 0 := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ
  have hD0 : dc h ≠ 0 := by
    simp only [dc]
    exact_mod_cast hΔ.ne'
  have p1 := hasFDerivAt_zpow_log (hasFDerivAt_dc h) (((k - 1 : ℕ)) : ℤ) hD0
  have p2 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-(2 * (k : ℤ) - 1)) hA0
  have p3 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-1 : ℤ) hA0
  have q := ((hasFDerivAt_be h).mul p3).const_mul (2 * Real.pi * Complex.I : ℂ)
  have e := q.cexp
  have t := (p1.mul p2).mul e
  have hw := HasFDerivAt.congr_of_eventuallyEq t (weight_eventually_closed_form k hk h hΔ)
  refine ⟨hw.differentiableAt, fun X => ?_⟩
  rw [hw.fderiv, weight_eq_closed_form k hk h hΔ]
  have c1 : ((((k - 1 : ℕ)) : ℤ) : ℂ) = (k : ℂ) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have c2 : ((-(2 * (k : ℤ) - 1) : ℤ) : ℂ) = 1 - 2 * (k : ℂ) := by
    push_cast
    ring
  have c3 : (((Matrix.of h).det : ℝ) : ℂ) = dc h := rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    dL_apply, colL_zero, colL_one, Pi.mul_apply, cl, ell, c1, c2, c3, zpow_neg_one,
    Int.cast_neg, Int.cast_one]
  clear hw t e q p1 p2 p3
  generalize Complex.exp _ = E
  generalize dc h ^ (((k - 1 : ℕ)) : ℤ) = P
  generalize al h ^ (-(2 * (k : ℤ) - 1)) = Q
  generalize al h = A at hA0 ⊢
  generalize dc h = D at hD0 ⊢
  field_simp
  ring

end GlobalTheory.CompanionTheory.DInt2.DerivW

theorem GlobalTheory.CompanionTheory.DInt2.dw0 : ∀ k : ℕ, 3 ≤ k → ∀ h : M22, 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X :=
  fun k hk h hΔ => GlobalTheory.CompanionTheory.DInt2.DerivW.main_deriv k hk h hΔ
