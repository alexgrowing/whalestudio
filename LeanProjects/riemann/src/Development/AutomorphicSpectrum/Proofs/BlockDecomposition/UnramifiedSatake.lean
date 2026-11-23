import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.AdmInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.Pack

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedGammaFactor

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def Un (μ : Fˣ →* ℂˣ) : Prop := ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1

end Loc

section Loc3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unr_mul {μ μ' : Fˣ →* ℂˣ} (h : IsUnramifiedChar μ) (h' : IsUnramifiedChar μ') :
    IsUnramifiedChar (μ * μ') := fun x hx => by
  have e1 : μ x = 1 := h hx
  have e2 : μ' x = 1 := h' hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, e1, e2, one_mul]

variable [MeasurableSpace F] [BorelSpace F]

end Loc3

section Glob

open scoped Classical

variable {K : Type} [Field K] [NumberField K]

theorem localChar_inv (c : HeckeCharacter K) (v : PlK K) : localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, GodementSection.coe_localChar, GodementSection.coe_localChar]
  rfl

def PT (DK : DatK K) (c : HeckeCharacter K) (T : Finset (PlK K)) (s : ℂ) : ℂ :=
  ∏ w ∈ T, lf3 (DK.ν w) (localChar c w) s

end Glob

section Main

open scoped Classical

end Main

end GlobalTheory.CompanionTheory.UnramifiedGammaFactor
