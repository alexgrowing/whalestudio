import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFunctionalLargeRankVanish
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_functional_large_rank_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), GlobalTheory.DetEqv.VanishAt k n → ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ), n + 1 < m →
    ∀ μ : kˣ →* ℂˣ, (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) → ∀ L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin m) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k)),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin m) k),
          (Φ' : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X * (g : Matrix (Fin m) (Fin m) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      (∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin m) k), X 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X) = 0) →
        L Φ = 0) →
      L = 0 := by
  first | exact @GlobalTheory.DetEqv.vanish_of_vanish_off_rowZero | exact GlobalTheory.DetEqv.vanish_of_vanish_off_rowZero | (intros; apply GlobalTheory.DetEqv.vanish_of_vanish_off_rowZero <;> assumption)
