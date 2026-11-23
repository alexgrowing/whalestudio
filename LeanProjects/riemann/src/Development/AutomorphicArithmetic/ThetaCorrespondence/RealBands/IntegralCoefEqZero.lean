import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvCoef
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ContinuousAverage
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.InvMemFlagN
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FlagNW
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroupStatement

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.integral_coef_eq_zero :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ v a : H,
        Decays (coefOn (ε := ε) σ v v) → Decays (coefOn (ε := ε) σ a v) →
        ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
          ∫ m, ⟪v, σ (umat (x * m * y)) a⟫_ℂ ∂ν = 0 := by
  intro n ε H _ _ σ hσ v a hvv hav W hW ν hν x y
  obtain ⟨hc, hn, hU, hI, hS⟩ := hσ
  obtain ⟨d, hd⟩ := GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS
  have hd0 : 0 < d := hd.1
  by_cases hv : v = 0
  · subst hv
    simp
  have hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0 := by positivity
  obtain ⟨hcvv, hconvvv⟩ := conv_coef n ε H σ d hU hd v v
  obtain ⟨hcav, hconvav⟩ := conv_coef n ε H σ d hU hd v a
  obtain ⟨hivv, -⟩ := continuous_average n ε _ hcvv hvv
  obtain ⟨hiav, hcontav⟩ := continuous_average n ε _ hcav hav
  obtain ⟨hν0, hνf, hνN, hνinv⟩ := hν
  haveI := hνf
  obtain ⟨hflag, h1, hNeq, S, hS⟩ := flagN_eq_NW n ε W hW
  obtain ⟨r, Hr, hr⟩ := exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)
  rw [hNeq] at hr
  set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk
  have hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1 := by
    rw [hk, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]
    simp
  have key := average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr
    (fun g => k * coefOn σ v v g) (coefOn σ a v)
    (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav
    (by
      intro z
      simp only [conv] at hconvvv ⊢
      have := hconvvv z
      simp only [mul_assoc]
      rw [show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z))))
          = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by
            funext g; ring]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (k * coefOn σ v v z) * hkc)
    (by
      intro z
      simp only [conv] at hconvav ⊢
      have := hconvav z
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (coefOn σ a v z) * hkc)
    x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y
  exact key
