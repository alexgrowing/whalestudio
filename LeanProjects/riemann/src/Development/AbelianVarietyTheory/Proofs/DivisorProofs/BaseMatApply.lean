import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil

namespace GlobalTheory.TypeTwo.FullRank

def baseMat (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin j) R :=
  Matrix.of fun i c => if (i : ℕ) = c then 1 else 0

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k]

def IsDens (ν : Measure k) {n j : ℕ} (μ : rkSB k n j j →ₗ[ℂ] ℂ) (ρ : Matrix (Fin n) (Fin j) k → ℂ) : Prop :=
  (∀ x : Matrix (Fin n) (Fin j) k, x.rank = j → ∀ᶠ y in nhds x, ρ y = ρ x) ∧
    ∀ Φ : rkSB k n j j, μ Φ = ∫ x, ρ x * Φ.1 x ∂(volM ν (Fin n) (Fin j))

end GlobalTheory.TypeTwo.FullRank
