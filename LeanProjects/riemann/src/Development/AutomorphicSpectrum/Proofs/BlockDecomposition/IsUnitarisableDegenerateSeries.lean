import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
