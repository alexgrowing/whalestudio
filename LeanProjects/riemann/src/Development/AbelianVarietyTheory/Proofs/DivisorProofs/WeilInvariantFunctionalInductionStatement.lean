import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilInvariantFunctionalInduction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_invariant_functional_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) (μ : kˣ →* ℂˣ)
    (L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k) →ₗ[ℂ] ℂ),
      (∀ (g : GL (Fin (m + 1)) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k)),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k),
          (Φ' : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      (∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k), X 0 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
        L Φ = 0) →
      ∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k), X 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
        L Φ = 0 := by
  first | exact @GlobalTheory.RowCut.eq_zero_of_row_vanish | exact GlobalTheory.RowCut.eq_zero_of_row_vanish | (intros; apply GlobalTheory.RowCut.eq_zero_of_row_vanish <;> assumption)
