import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addValuation_natCast_eq_padicValNat' : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 → v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  first | exact @GlobalTheory.addValuation_natCast_eq_padicValNat | exact GlobalTheory.addValuation_natCast_eq_padicValNat | (intros; apply GlobalTheory.addValuation_natCast_eq_padicValNat <;> assumption)
