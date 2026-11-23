import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
