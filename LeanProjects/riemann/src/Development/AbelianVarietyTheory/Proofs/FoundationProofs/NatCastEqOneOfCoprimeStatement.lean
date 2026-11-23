import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_of_coprime' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  first | exact @GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | exact GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | (intros; apply GlobalTheory.AlmostEt.natCast_eq_one_of_coprime <;> assumption)
