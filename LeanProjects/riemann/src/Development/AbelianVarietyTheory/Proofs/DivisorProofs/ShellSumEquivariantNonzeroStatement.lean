import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shell_sum_equivariant_nonzero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (n e : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsUnif ϖ → IsSmU ν → ¬ IsUnram ν → CondLE ϖ e ν →
    IsEqv ν z (shellSum (haarVol (KO k (Fin n))) ϖ ν z) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), shellSum (haarVol (KO k (Fin n))) ϖ ν z φ ≠ 0 := by
  first | exact @GlobalTheory.ShellSumEqv.shellSum_isEqv_and_ne_zero | exact GlobalTheory.ShellSumEqv.shellSum_isEqv_and_ne_zero | (intros; apply GlobalTheory.ShellSumEqv.shellSum_isEqv_and_ne_zero <;> assumption)
