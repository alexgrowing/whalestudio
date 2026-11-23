import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r → ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  first | exact @GlobalTheory.IwConst.CloseLevi.close_levi | exact GlobalTheory.IwConst.CloseLevi.close_levi | (intros; apply GlobalTheory.IwConst.CloseLevi.close_levi <;> assumption)
