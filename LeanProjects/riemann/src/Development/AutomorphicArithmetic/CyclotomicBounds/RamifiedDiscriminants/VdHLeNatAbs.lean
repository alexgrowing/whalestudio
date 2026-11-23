import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

theorem Formalism.HC.HostRaw.vdH_le_natAbs {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) :
    H.vdH p ≤ ((NumberField.discr H.E).natAbs : ℝ) := by
  unfold Formalism.HC.HostRaw.vdH
  have h1 : (1 : ℝ) ≤ (Module.finrank ℚ H.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have h2 : padicValNat p (NumberField.discr H.E).natAbs ≤ (NumberField.discr H.E).natAbs :=
    (padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)
  have h3 : (padicValNat p (NumberField.discr H.E).natAbs : ℝ) ≤ ((NumberField.discr H.E).natAbs : ℝ) := by exact_mod_cast h2
  exact (div_le_self (Nat.cast_nonneg _) h1).trans h3
