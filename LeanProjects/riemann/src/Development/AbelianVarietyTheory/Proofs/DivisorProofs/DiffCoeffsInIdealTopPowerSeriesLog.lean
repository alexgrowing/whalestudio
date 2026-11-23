import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.QLog

namespace GlobalTheory.QLog.LogDiff

theorem dIn_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q],
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro B Q _ _ _ _ α i
  have hc : MvPowerSeries.coeff α (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (α i) (PowerSeries.log Q) := by
    rw [PowerSeries.coeff_def (s := α) (n := α i) rfl]
  rw [hc, PowerSeries.coeff_log]
  by_cases h : α i = 0
  · exact ⟨0, trivial, by simp [h]⟩
  · refine ⟨(-1) ^ (α i + 1), trivial, ?_⟩
    have h' : ((α i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [if_neg h, ← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

end GlobalTheory.QLog.LogDiff
