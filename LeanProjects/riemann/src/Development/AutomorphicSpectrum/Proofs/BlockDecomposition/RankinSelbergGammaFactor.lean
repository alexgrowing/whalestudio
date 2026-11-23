import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.TateGamma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exponent_eq_zero {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) : quasiCharExponent c = 0 := by
  simp [quasiCharExponent, hc.2]

theorem isUnit1_inv {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) : Ad3.IsUnit1 c⁻¹ :=
  ⟨continuous_quasiChar_inv hc.1, fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hc.2, inv_one]⟩

theorem lFactor_ne_zero {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    localLFactor c s ≠ 0 :=
  localLFactor_ne_zero hc.1 (by rw [exponent_eq_zero hc]; simpa using hs)

theorem differentiableAt_lFactor {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (localLFactor c) s := by
  by_cases h : IsUnramifiedChar c
  · have e : localLFactor c =
        fun s => (1 - ((c (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ :=
      funext fun s => localLFactor_of_isUnramified h s
    rw [e]
    refine DifferentiableAt.inv ?_ ?_
    · exact (((differentiable_qpow (K := F)).const_mul _).const_sub 1) s
    · exact one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hc.1
        (by rw [exponent_eq_zero hc]; simpa using hs)
  · have e : localLFactor c = fun _ => (1 : ℂ) :=
      funext fun s => localLFactor_of_not_isUnramified h s
    rw [e]
    exact differentiableAt_const _

theorem gam_strip : Ad3.R.LocalGammaFunctionalEquation := by
  intro F _ _ _ _ _ _ ψ hψ c hc
  have hc' := isUnit1_inv hc
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have h1 : 0 < (1 - s).re := by
      have := hs.2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hL : DifferentiableAt ℂ (fun s => localLFactor c⁻¹ (1 - s)) s :=
      DifferentiableAt.comp (f := fun s : ℂ => 1 - s) s (differentiableAt_lFactor hc' h1)
        ((differentiableAt_const _).sub differentiableAt_id)
    have hg : DifferentiableAt ℂ (Ad3.gam ψ c) s := by
      unfold Ad3.gam
      exact ((differentiable_localEpsilon s).mul hL).div (differentiableAt_lFactor hc hs.1)
        (lFactor_ne_zero hc hs.1)
    exact hg.differentiableWithinAt
  · have h0 : 0 < s.re := hs.1
    have h1 : 0 < (1 - s).re := by
      have := hs.2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hL := lFactor_ne_zero hc h0
    have hL' := lFactor_ne_zero hc' h1
    have hε := localEpsilon_mul_localEpsilon_inv_eq_of_strip (χ := c) hψ.1 hψ.2.1 hc.1
      (s := s) (by rw [exponent_eq_zero hc]; simpa using h0)
      (by rw [exponent_eq_zero hc]; simpa using hs.2)
    have hcc : (c⁻¹)⁻¹ = c := inv_inv c
    unfold Ad3.gam
    rw [hcc, sub_sub_cancel, ← hε]
    field_simp

end GlobalTheory.CompanionTheory.TateGamma

end
