import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OmegaColumnSlices
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices

namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices

theorem hat_mem_SB_and_hat_omCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k), HasConductor ψ 1 → IsUnitVol ν → valuation k ε = 1 → ∀ (n : Type) [Fintype n] [DecidableEq n] (μz : kˣ →* ℂˣ) (h : GL n k), ∀ φ ∈ SB (n → k), hat ψ ν ε φ ∈ SB (n → k) ∧ hat ψ ν ε (omCol μz h φ) = omRow μz h (hat ψ ν ε φ) := by
  intro k _ _ _ _ _ _ ψ ν ε hψ hν hε n _ _ μz h φ hφ
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  constructor
  · have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hψ hφ
    have e : hat ψ ν ε φ = (fun y : n → k => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) ∘
        (Homeomorph.smulOfNeZero ε hε0 : (n → k) ≃ₜ (n → k)) := by
      funext η
      simp only [hat, Function.comp, Homeomorph.smulOfNeZero_apply, dotProduct_smul, smul_eq_mul,
        dotProduct_comm η]
    rw [e]
    exact ⟨hF.1.comp_continuous (Homeomorph.continuous _), hF.2.comp_homeomorph _⟩
  · funext η
    have key := integral_comp_mulVec_eq_smul ν h⁻¹ (fun y => φ y * (ψ (ε * ((η ᵥ* h.val) ⬝ᵥ y)) : ℂ))
    have e1 : ∀ y : n → k, (η ᵥ* h.val) ⬝ᵥ ((h⁻¹).val *ᵥ y) = η ⬝ᵥ y := by
      intro y
      rw [← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    simp only [e1] at key
    have hp := nabs_pos' (Matrix.GeneralLinearGroup.det h)
    have e2 : (nabs k (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det h) := by
      simp [nabs]
    have e3 : nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) * nabs k (Matrix.GeneralLinearGroup.det h) =
        nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add_one hp.ne']
      norm_num
    simp only [hat, omCol, omRow, mul_assoc, integral_const_mul]
    rw [key, e2, ← e3, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
