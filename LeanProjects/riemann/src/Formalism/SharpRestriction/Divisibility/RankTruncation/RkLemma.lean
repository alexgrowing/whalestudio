import Mathlib

noncomputable section

namespace ConditionalKappaBounds.Rk

def RkProp : Prop := ∀ (dp f m r t : ℕ) (x Ct q d rd CRd : ℝ), 1 < x → 6 ≤ CRd →
  dp ≤ 2 * f * m → f ≤ r → m ≤ r → r < t → 2 ≤ t → (t : ℝ) ≤ x ^ Ct →
  x ^ (2 * Ct + 5) < q → x ^ (2 * Ct + 5) < d → Real.sqrt (q * d) ≤ rd →
  (dp : ℝ) ^ 2 ≤ rd ^ (CRd - 2)

end ConditionalKappaBounds.Rk
