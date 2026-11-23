import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitWeilEquivariantFunctionalBlock
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_equivariant_functional_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x m n : ℕ), GlobalTheory.DetEqv.VanishAt k n → n < m → ∀ μ : kˣ →* ℂˣ, (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) →
    ∀ L : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + m)) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (![x, m] 1)) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + m)) k)),
        (∀ X : Matrix (Fin n) (Fin (x + m)) k, (Φ' : Matrix (Fin n) (Fin (x + m)) k → ℂ) X =
          (Φ : Matrix (Fin n) (Fin (x + m)) k → ℂ) (X * ((GlobalTheory.SmGL.leviEmb k (GlobalTheory.ThK.MidJac.e2 x m)
            (Pi.mulSingle (1 : Fin 2) g) : GL (Fin (x + m)) k) : Matrix (Fin (x + m)) (Fin (x + m)) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      L = 0 := by
  first | exact @GlobalTheory.DetEqv.BlockForm.eq_zero_of_vanishAt | exact GlobalTheory.DetEqv.BlockForm.eq_zero_of_vanishAt | (intros; apply GlobalTheory.DetEqv.BlockForm.eq_zero_of_vanishAt <;> assumption)
