import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerTrans

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mp_mul' (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem continuous_vecMul_gl (k : GL (Fin 2) F) :
    Continuous fun x : Fin 2 → F ↦ x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) :=
  continuous_id.matrix_vecMul continuous_const

def vecMulHomeo (k : GL (Fin 2) F) : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun x := x ᵥ* (k : Matrix (Fin 2) (Fin 2) F)
  invFun x := x ᵥ* ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  left_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := continuous_vecMul_gl k
  continuous_invFun := continuous_vecMul_gl k⁻¹

theorem rt_mem {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F)
    (k : GL (Fin 2) F) : rt φ k ∈ GodementSectionLocal.schwartzBruhat2 F :=
  ⟨hφ.1.comp_continuous (continuous_vecMul_gl k),
    hφ.2.comp_isClosedEmbedding (vecMulHomeo k).isClosedEmbedding⟩

variable [MeasurableSpace F] [BorelSpace F]

theorem whittaker_right_translation_formula (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ)
    (g h : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (g * h) = ((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det h) (1 / 2) * W2 ψ μ₁ μ₂ (rt φ h) g := by
  simp only [W2, rt, map_mul, Units.val_mul, mp_mul', Matrix.vecMul_vecMul]
  ring

theorem sTrans : Ad3.SchwartzSpaceL2.STrans := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ hφ h
  exact ⟨rt_mem hφ h, fun g => whittaker_right_translation_formula ψ μ₁ μ₂ φ g h⟩

end GlobalTheory.CompanionTheory.WhittakerTrans
