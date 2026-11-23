import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDisc
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletL_few_zeros_small_disc : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (1 + t * I) r, (ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  first | exact @GlobalTheory.SmallDiscZeros.few_zeros | exact GlobalTheory.SmallDiscZeros.few_zeros | (intros; apply GlobalTheory.SmallDiscZeros.few_zeros <;> assumption)
