import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

theorem fderiv_eq_of_dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x y : V) :
    fderiv ℝ g x y = 2 * fockForm β J x y * g x := by
  have h := heq (0, Ring.inverse (blockB J) y) x
  have h1 : (J (0, Ring.inverse (blockB J) y)).1 = y := by
    rw [← blockB_apply, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hB]; rfl
  have h2 : (J (0, Ring.inverse (blockB J) y)).2 = blockD J (Ring.inverse (blockB J) y) := rfl
  simp only [GlobalTheory.GaussLine.dHeis, h1, h2, map_zero, zero_sub] at h
  rw [fockForm_apply]
  push_cast
  linear_combination h - 2 * Real.pi * (β x (Ring.inverse (blockB J) y) : ℂ) * g x * Complex.I_sq

theorem solution_eq_gauss {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (hg : Differentiable ℝ g)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x : V) :
    g x = g 0 * Complex.exp (fockForm β J x x) := by
  set c : ℂ := fockForm β J x x with hc
  let h : ℝ → ℂ := fun s => g (s • x) * Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c)
  have hd : ∀ s : ℝ, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (s • x) x) s := by
      have := (hg (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
      simp only [one_smul] at this
      exact this
    have e2 : HasDerivAt (fun t : ℝ => Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c))
        (Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c) * (-((((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1 : ℝ) : ℂ) * c)) s := by
      exact ((((hasDerivAt_id s).pow 2).ofReal_comp).neg.mul_const c).cexp
    have hf : fderiv ℝ g (s • x) x = 2 * ((s : ℂ) * c) * g (s • x) := by
      rw [fderiv_eq_of_dHeis β J hB g heq, map_smul, LinearMap.smul_apply, Complex.real_smul]
    show HasDerivAt (fun t : ℝ => g (t • x) * Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c)) 0 s
    refine (e1.mul e2).congr_deriv ?_
    rw [hf]
    push_cast
    ring
  have hconst : ∀ a b : ℝ, h a = h b := fun a b =>
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) a b
  have := hconst 1 0
  simp only [h, one_smul, zero_smul, one_pow, Complex.ofReal_one, neg_mul, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.FockFamily

end
