import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

theorem TelescopeMetric.le_first {n : ℕ} {I : ℕ → ℝ} (h : ∀ i, i < n → I (i + 1) ≤ I i) :
    ∀ i, i ≤ n → I i ≤ I 0 := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    exact (h k (by omega)).trans (ih (by omega))

theorem TelescopeMetric.proof : TelescopeMetric.Statement := by
  intro n A A' I h
  have hsum : ∑ i ∈ Finset.range (n + 1), I i ≤ (n + 1) * I 0 := by
    have := Finset.sum_le_sum (s := Finset.range (n + 1)) (f := I) (g := fun _ => I 0)
      (fun i hi => TelescopeMetric.le_first h.antitone i (by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hi))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have := h.sum_eq
  linarith

end GroundTheory.Heights₂.Heights.LowerBound
