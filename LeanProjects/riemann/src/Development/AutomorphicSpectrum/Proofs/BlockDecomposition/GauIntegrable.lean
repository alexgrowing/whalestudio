import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

def cat (A : M22) (y : Fin 2 → ℝ) : M23 := fun r => ![A r 0, A r 1, y r]

def fz (Φ : Sw) (A : M22) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ y : Fin 2 → ℝ, Φ (cat A y) * Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))

def gz (Φ : Sw) (h : M22) (ζ : ℝ) : ℂ :=
  ∫ z : Fin 2 → ℝ, Φ (Matrix.of.symm (Matrix.of h * blk z)) *
    Complex.exp (2 * Real.pi * Complex.I * ((ζ * z 0 + z 1 : ℝ) : ℂ))

def dualF (h : M22) (ζ : ℝ) : Fin 2 → ℝ :=
  ![(h 1 1 * ζ - h 1 0) / (Matrix.of h).det, (h 0 0 - h 0 1 * ζ) / (Matrix.of h).det]

def gau (ε ζ : ℝ) : ℝ := ε⁻¹ * Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2)

def wt (a l ζ : ℝ) : ℝ := ((1 + |ζ - l| / a) ^ 2)⁻¹

lemma wt_nonneg (a l ζ : ℝ) : 0 ≤ wt a l ζ := inv_nonneg.2 (sq_nonneg _)

lemma gau_nonneg (ε ζ : ℝ) (hε : 0 < ε) : 0 ≤ gau ε ζ :=
  mul_nonneg (inv_nonneg.2 hε.le) (Real.exp_pos _).le

lemma gau_eq (ε ζ : ℝ) : gau ε ζ = ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := by
  unfold gau; congr 2; ring

lemma gau_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (gau ε) := by
  have : gau ε = fun ζ => ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := funext (gau_eq ε)
  rw [this]
  exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _

lemma gau_integral (ε : ℝ) (hε : 0 < ε) : ∫ ζ, gau ε ζ = 1 := by
  have : gau ε = fun ζ => ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := funext (gau_eq ε)
  rw [this, integral_const_mul, integral_gaussian]
  have : Real.pi / (Real.pi / ε ^ 2) = ε ^ 2 := by
    field_simp
  rw [this, Real.sqrt_sq hε.le]
  field_simp

end GlobalTheory.CompanionTheory.Parseval
