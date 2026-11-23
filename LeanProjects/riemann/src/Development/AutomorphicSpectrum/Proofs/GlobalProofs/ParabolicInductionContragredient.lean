import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

namespace GlobalTheory.CompanionTheory.Glob

theorem inductionContragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k :=
  GlobalTheory.SmGL.IndDual.inductionContragredient

end GlobalTheory.CompanionTheory.Glob
