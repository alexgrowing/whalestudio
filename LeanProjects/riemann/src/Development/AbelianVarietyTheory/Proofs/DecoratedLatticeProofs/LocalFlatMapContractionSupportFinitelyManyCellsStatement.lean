import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapContractionSupportFinitelyManyCells
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMapContraction_support_finitelyManyCells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    IsSelfDual ψ ν → ∀ (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ μ' : kˣ →* ℂˣ) (J : Subgroup (GL (n₂ ⊕ Fin c) k)),
    IsOpen (J : Set (GL (n₂ ⊕ Fin c) k)) → ∀ (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))
    (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (a : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (x : GL (n₁ ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n₂ ⊕ Fin c) k), ∀ y : GL (n₂ ⊕ Fin c) k,
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (om μ a x Φ₁.1)) (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) ≠ 0 →
      ∃ r ∈ R k n₂ c ρ, ∃ t ∈ T, ∃ j ∈ J, y = r * t * j := by
  first | exact @GlobalTheory.LocFlat.contr_support_finite_cells | exact GlobalTheory.LocFlat.contr_support_finite_cells | (intros; apply GlobalTheory.LocFlat.contr_support_finite_cells <;> assumption)
