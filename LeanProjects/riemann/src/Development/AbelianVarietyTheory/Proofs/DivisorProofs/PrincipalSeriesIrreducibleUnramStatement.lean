import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesIrreducibleUnram
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_irreducible_unram : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ →
    μ₁ ≠ μ₂ * GlobalTheory.SmGL.absPow k 1 → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 →
    (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂)).IsIrreducible := by
  first | exact @GlobalTheory.PrinTwo.Irr.isIrreducible_prod₂ | exact GlobalTheory.PrinTwo.Irr.isIrreducible_prod₂ | (intros; apply GlobalTheory.PrinTwo.Irr.isIrreducible_prod₂ <;> assumption)
