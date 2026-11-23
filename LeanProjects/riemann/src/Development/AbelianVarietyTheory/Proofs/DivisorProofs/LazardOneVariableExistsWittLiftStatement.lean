import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardOneVariableExistsWittLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lazard_one_variable_exists_witt_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ) (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) → (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) → ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k, t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧ WittVector.constantCoeff w = a i := by
  first | exact @GlobalTheory.LazardOne.exists_lift | exact GlobalTheory.LazardOne.exists_lift | (intros; apply GlobalTheory.LazardOne.exists_lift <;> assumption)
