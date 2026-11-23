import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerCentral

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem mp_one_left (s : ℂ) : mp (1 : Fˣ) s = 1 := by
  simp [mp, modulus_one]

theorem mp_half_mul_self (a : Fˣ) : mp a (1 / 2) * mp a (1 / 2) = mp a 1 := by
  have h : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero a.ne_zero)
  simp only [mp]
  rw [← Complex.cpow_add _ _ h]
  norm_num

theorem mp_inv_mul_self (a : Fˣ) (s : ℂ) : mp a⁻¹ s * mp a s = 1 := by
  rw [← mp_mul, inv_mul_cancel, mp_one_left]

theorem det_scalar_diagonal_mul (a : Fˣ) (g : GL (Fin 2) F) :
    GeneralLinearGroup.det (dg2 a a * g) = a * a * GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  ext
  simp [dg2, GeneralLinearGroup.det, Matrix.det_fin_two]

theorem row_vector_scalar_diagonal_mul (a h : Fˣ) (x : F) (g : GL (Fin 2) F) :
    ![(h : F), h * x] ᵥ* ((dg2 a a * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ![((a * h : Fˣ) : F), ((a * h : Fˣ) : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem whittaker_central_character_equivariance (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (a : Fˣ)
    (g : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (dg2 a a * g) = ((μ₁ a * μ₂ a : ℂˣ) : ℂ) * W2 ψ μ₁ μ₂ φ g := by
  set Φ : Fˣ → ℂ := fun h => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ)
        ∂selfDualMeasure ψ) with hΦ
  have hint : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* ((dg2 a a * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F =
      (((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * mp a⁻¹ 1) * ∫ h : Fˣ, Φ h ∂multHaar F := by
    rw [← integral_mul_left_eq_self Φ a, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hΦ, row_vector_scalar_diagonal_mul]
    have e : (((μ₁ (a * h))⁻¹ * μ₂ (a * h) : ℂˣ) : ℂ) =
        ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ)⁻¹ * (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, map_mul, map_mul]
      congr 1
      simp only [mul_inv, inv_inv]
      exact mul_mul_mul_comm _ _ _ _ |>.trans (by simp [mul_comm, mul_left_comm, mul_assoc])
    rw [e, mp_mul]
    have hc : ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Units.ne_zero _)
    have hN : mp a⁻¹ 1 * mp a 1 = 1 := mp_inv_mul_self a 1
    generalize ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) = c at hc ⊢
    generalize mp a⁻¹ 1 = N at hN ⊢
    generalize mp a 1 = M at hN ⊢
    generalize (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) = X
    generalize mp h 1 = m
    generalize (∫ x, φ (![((a * h : Fˣ) : F), ((a * h : Fˣ) : F) * x] ᵥ*
      (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) = I
    linear_combination (-(N * M * X * m * I)) * hc + (-(X * m * I)) * hN
  have hWg : W2 ψ μ₁ μ₂ φ g = ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det g) (1 / 2) * ∫ h : Fˣ, Φ h ∂multHaar F := rfl
  have hWa : W2 ψ μ₁ μ₂ φ (dg2 a a * g) =
      ((μ₂ (a * a * GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        mp (a * a * GeneralLinearGroup.det g) (1 / 2) *
        ((((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * mp a⁻¹ 1) * ∫ h : Fˣ, Φ h ∂multHaar F) := by
    rw [← hint, ← det_scalar_diagonal_mul]
    rfl
  rw [hWa, hWg, mp_mul, mp_mul, mp_half_mul_self, map_mul, map_mul]
  have hB : ((μ₂ a : ℂˣ) : ℂ) * (((μ₂ a)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : mp a⁻¹ 1 * mp a 1 = 1 := mp_inv_mul_self a 1
  simp only [Units.val_mul]
  generalize (((μ₂ a)⁻¹ : ℂˣ) : ℂ) = B' at hB ⊢
  generalize ((μ₂ a : ℂˣ) : ℂ) = B at hB ⊢
  generalize mp a⁻¹ 1 = N at hN ⊢
  generalize mp a 1 = M at hN ⊢
  generalize ((μ₁ a : ℂˣ) : ℂ) = A
  generalize ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = D
  generalize mp (GeneralLinearGroup.det g) (1 / 2) = P
  generalize (∫ h : Fˣ, Φ h ∂multHaar F) = J
  linear_combination (B * B * B' * D * P * A * J) * hN + (B * D * P * A * J) * hB

theorem sCen : Ad3.SchwartzSpaceL2.SCen := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ _ a g
  exact whittaker_central_character_equivariance ψ μ₁ μ₂ φ a g

end GlobalTheory.CompanionTheory.WhittakerCentral
