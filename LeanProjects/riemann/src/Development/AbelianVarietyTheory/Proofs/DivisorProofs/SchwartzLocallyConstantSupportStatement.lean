import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLocallyConstantSupport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_locally_constant_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ φ : Matrix (Fin n) (Fin n) k → ℂ, φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ N M : ℕ, (∀ X, φ X ≠ 0 → t ^ N • X ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X E, E ∈ intM k (Fin n) (Fin n) → φ (X + t ^ M • E) = φ X := by
  first | exact @GlobalTheory.SBBounds.sb_bounds | exact GlobalTheory.SBBounds.sb_bounds | (intros; apply GlobalTheory.SBBounds.sb_bounds <;> assumption)
