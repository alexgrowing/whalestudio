import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_principal_series_no_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 := by
  first | exact @GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed | exact GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed | (intros; apply GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed <;> assumption)
