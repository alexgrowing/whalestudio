import Mathlib

namespace GlobalTheory.AbelianSumIdentityThird

theorem main : ∀ {S : Type} [inst : Ring S] (ε a b Gi K : S), (∀ (x : S), ε * x = x * ε) → ε * ε = ε → ε * a = a → ε * b = b → ((1 : S) - K) * a = ε → a * ((1 : S) - K) = ε → ((1 : S) - Gi * K) * b = ε → b * ((1 : S) - Gi * K) = ε → ((1 : S) - ε + b * ((1 : S) - K)) * ((1 : S) - ε + a * ((1 : S) - Gi * K)) = (1 : S) ∧ ((1 : S) - ε + a * ((1 : S) - Gi * K)) * ((1 : S) - ε + b * ((1 : S) - K)) = (1 : S) := by
  intro S _ ε a b Gi K hc hε ha hb h1 h2 h3 h4
  have haε : a * ε = a := by rw [← hc]; exact ha
  have hbε : b * ε = b := by rw [← hc]; exact hb
  have t1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  have t2a : (1 - ε) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
  have t2b : (1 - ε) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
  have t3 : ∀ x y : S, x * ε = x → x * y * (1 - ε) = 0 := by
    intro x y hx
    rw [mul_sub, mul_one, mul_assoc, ← hc y, ← mul_assoc, hx, sub_self]
  constructor
  · have e : b * (1 - K) * (a * (1 - Gi * K)) = ε := by
      rw [← mul_assoc, mul_assoc b, h1, hbε, h4]
    calc (1 - ε + b * (1 - K)) * (1 - ε + a * (1 - Gi * K))
        = (1 - ε) * (1 - ε) + (1 - ε) * a * (1 - Gi * K) + b * (1 - K) * (1 - ε)
          + b * (1 - K) * (a * (1 - Gi * K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2a, t3 b _ hbε, e]; noncomm_ring
  · have e : a * (1 - Gi * K) * (b * (1 - K)) = ε := by
      rw [← mul_assoc, mul_assoc a, h3, haε, h2]
    calc (1 - ε + a * (1 - Gi * K)) * (1 - ε + b * (1 - K))
        = (1 - ε) * (1 - ε) + (1 - ε) * b * (1 - K) + a * (1 - Gi * K) * (1 - ε)
          + a * (1 - Gi * K) * (b * (1 - K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2b, t3 a _ haε, e]; noncomm_ring

end GlobalTheory.AbelianSumIdentityThird
