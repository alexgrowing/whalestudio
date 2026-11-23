import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

def thrDS {n : ℕ} (ε : Fin n → Bool) : ℝ := (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1

theorem pOf_le {n : ℕ} (ε : Fin n → Bool) : pOf ε ≤ n := by
  unfold pOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem qOf_le {n : ℕ} (ε : Fin n → Bool) : qOf ε ≤ n := by
  unfold qOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem thrDS_le {n : ℕ} (ε : Fin n → Bool) : thrDS ε ≤ (n : ℝ) ^ 3 + 1 := by
  unfold thrDS
  have hp : (pOf ε : ℝ) ≤ n := by exact_mod_cast pOf_le ε
  have hq : (qOf ε : ℝ) ≤ n := by exact_mod_cast qOf_le ε
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  have : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) * n * n :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp h0) hq h2 (mul_nonneg h0 h0)
  nlinarith

end Formalism.MainNotions.GapDS

end
