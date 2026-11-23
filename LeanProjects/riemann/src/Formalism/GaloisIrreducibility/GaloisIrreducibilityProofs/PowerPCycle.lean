import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

theorem power_of_p_cycle : PowerPCycle := by
  intro α _ _ σ p hp hmem hcard
  have hdvd : p ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hmem
  have hpos : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  refine ⟨orderOf σ / p, ?_⟩
  have hord : orderOf (σ ^ (orderOf σ / p)) = p := orderOf_pow_orderOf_div hpos hdvd
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ ^ (orderOf σ / p)) (by rw [hord]; exact hp)
  rw [hord] at hn
  have hsum : (σ ^ (orderOf σ / p)).support.card = (n + 1) * p := by
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul]
  have hle : (σ ^ (orderOf σ / p)).support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    have h3 : 2 * p ≤ Fintype.card α := h2.trans (hsum ▸ hle)
    omega
  subst hn0
  refine ⟨?_, by rw [hsum]; ring⟩
  rw [← Equiv.Perm.card_cycleType_eq_one, hn]
  simp

end Formalism.GaloisIrreducibility
