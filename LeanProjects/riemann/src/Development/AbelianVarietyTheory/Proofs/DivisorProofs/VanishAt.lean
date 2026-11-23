import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

namespace GlobalTheory.DetEqv

def VanishAt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ), n < m → ∀ μ : kˣ →* ℂˣ,
    (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) →
    ∀ L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin n) (Fin m) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin m) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin n) (Fin m) k)),
        (∀ (y : Y) (X : Matrix (Fin n) (Fin m) k),
          (Φ' : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, X * (g : Matrix (Fin m) (Fin m) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      L = 0

end GlobalTheory.DetEqv
