import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNonzeroAtOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_principal_series_nonzero_at_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → ∃ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, GlobalTheory.PrinTwo.ev f 1 ≠ 0 := by
  first | exact @GlobalTheory.PrinTwo.exists_ev_one_ne_zero | exact GlobalTheory.PrinTwo.exists_ev_one_ne_zero | (intros; apply GlobalTheory.PrinTwo.exists_ev_one_ne_zero <;> assumption)
