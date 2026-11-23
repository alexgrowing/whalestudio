import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def kavg [MeasurableSpace (Kinf E a)] (ν : Measure (Kinf E a)) (F : GL (Fin a) (Cinf E) → ℂ)
    (y : GL (Fin a) (Cinf E)) : ℂ :=
  ∫ k, F (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) ∂ν

variable [IsTotallyComplex E]

def liftInf (F : GL (Fin a) (Cinf E) → ℂ) : GA E a → ℂ := fun x => F (Matrix.GeneralLinearGroup.map (pInf E) x)

variable (E a) in

def sphSpace (W₁ W₂ : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) :
    Set (GL (Fin a) (Cinf E) → ℂ) :=
  {F | ∃ h : liftInf F ∈ Sm E a, (∀ y, (fun k : Kinf E a => F (Unitary.toUnits k * y)) ∈ W₁) ∧
    (∀ y, (fun k : Kinf E a => F (y * Unitary.toUnits k)) ∈ W₂) ∧ ∃ χ ∈ X, GlobalTheory.HCF.CentralNilGL χ N ⟨liftInf F, h⟩}

end GlobalTheory.HCAlphaGL

end
