import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CharDual

variable {F : Type} [Field F] [NumberField F]

def toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar (AF F) Circle where
  toFun x := ⟨ψ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact ψ.map_add_eq_mul a b

theorem coe_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : AF F) :
    ((toCircle ψ h x : Circle) : ℂ) = ψ x := rfl

theorem continuous_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ) :
    Continuous (toCircle ψ h) :=
  Continuous.subtype_mk hc _

theorem exists_eq_adelicChar_mul (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ ξ : F, ξ ≠ 0 ∧ ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := by
  obtain ⟨hc, hn, hF, x₀, hx₀⟩ := hψ
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul (toCircle ψ hn)
    (continuous_toCircle ψ hn hc) (fun k => Circle.ext (by simpa [coe_toCircle] using hF k))
  have key : ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := fun x => by
    rw [← hξ x, coe_toCircle]
  refine ⟨ξ, ?_, key⟩
  rintro rfl
  apply hx₀
  rw [key x₀]
  simp

theorem exists_scalar (ψ ψ' : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (hψ' : IsCharAF F ψ') :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_eq_adelicChar_mul ψ hψ
  obtain ⟨η, hη0, hη⟩ := exists_eq_adelicChar_mul ψ' hψ'
  refine ⟨η / ξ, div_ne_zero hη0 hξ0, fun x => ?_⟩
  have hc : ξ * (η / ξ) = η := by field_simp
  rw [hη x, hξ, ← mul_assoc, ← map_mul, hc]

end GlobalTheory.CompanionTheory.SW.CharDual

theorem GlobalTheory.CompanionTheory.SW.char_dual : ∀ (F : Type) [Field F] [NumberField F] (ψ ψ' : AddChar (AF F) ℂ),
    IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) :=
  fun _ _ _ ψ ψ' hψ hψ' => GlobalTheory.CompanionTheory.SW.CharDual.exists_scalar ψ ψ' hψ hψ'
