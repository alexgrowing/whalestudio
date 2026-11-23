import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.brunTitchmarsh_exists_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  first | exact @GlobalTheory.Lin.brun_titchmarsh_const | exact GlobalTheory.Lin.brun_titchmarsh_const | (intros; apply GlobalTheory.Lin.brun_titchmarsh_const <;> assumption)
