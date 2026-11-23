import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelbergRotation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def rotHomeo : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun r := ![r 1, -r 0]
  invFun r := ![-r 1, r 0]
  left_inv r := by
    funext i
    fin_cases i <;> simp
  right_inv r := by
    funext i
    fin_cases i <;> simp
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop

variable [MeasurableSpace F] [BorelSpace F]

theorem sF_eq (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) :
    sF ψ φ = fun r => GJMatrix.localFourierPi ψ φ (rotHomeo r) := by
  funext r
  have h : ∀ r' : Fin 2 → F, dt r' r = ∑ i, r' i * (rotHomeo r) i := by
    intro r'
    simp [dt, rotHomeo, Fin.sum_univ_two, sub_eq_add_neg]
  simp only [sF, GJMatrix.localFourierPi, h]
  rfl

theorem sF_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    SB (sF ψ φ) := by
  have h : GJMatrix.localFourierPi ψ φ ∈ GJMatrix.localSchwartzBruhatPi F :=
    GJMatrix.localFourierPi_mem hψ.1 hψ.2.1 hφ
  rw [sF_eq]
  exact ⟨h.1.comp_continuous rotHomeo.continuous, h.2.comp_homeomorph rotHomeo⟩

theorem whittakerGL2_smul_eq (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (z : ℂ) :
    W2 ψ μ₁ μ₂ (z • φ) = z • W2 ψ μ₁ μ₂ φ := by
  funext g
  simp only [W2, Pi.smul_apply, smul_eq_mul, mul_assoc z, integral_const_mul]
  have e : ∀ (a b c : ℂ), a * b * (z * c) = z * (a * b * c) := fun a b c => by ring
  simp only [e, integral_const_mul]

theorem a1 : Ad3.R.A1 := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ φ h hφ
  exact ⟨GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hφ h, sF_mem hψ hφ, whittakerGL2_smul_eq ψ μ₁ μ₂ φ,
    fun g => GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula ψ μ₁ μ₂ φ g h⟩

end GlobalTheory.CompanionTheory.RankinSelbergRotation

end
