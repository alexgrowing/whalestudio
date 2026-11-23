import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityOfVanishingPowersStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_lead_orders_eq : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C))
    (ξ : R) (N : ℕ) (a : ι → ℕ) (c c' : ι → C) (Δ Δ' u u' g g' g₁ : R),
    ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) →
    (∀ i, a i ≤ N) → (∀ i, c i ≠ 0) → (∀ i, Lead (f i) ξ Δ (a i) (c i)) →
    (∀ i, Lead (f i) ξ Δ' (a i) (c' i)) → Δ = g * u → Δ' = g' * u' → (∀ i, f i u' ≠ 0) →
    g * g₁ = ξ ^ N → g ∣ g' := by
  intro R C ι _ _ f ξ N a c c' Δ Δ' u u' g g' g₁ hξ hf0 hker haN hc hL hL' hΔ hΔ' hu' hgg
  have hpow : ∀ n : ℕ, ξ ^ n ∈ nonZeroDivisors R := fun n => pow_mem hξ n
  have hloc : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ N ∣ s * (g' * g₁) := by
    intro i
    obtain ⟨s, t, hs, hst, hft⟩ := hL i
    obtain ⟨s', t', hs', hst', -⟩ := hL' i
    have ht : f i t ≠ 0 := by rw [hft]; exact mul_ne_zero (hc i) hs
    have hsplit : ξ ^ a i * ξ ^ (N - a i) = ξ ^ N := pow_mul_pow_sub ξ (haN i)
    have key : t * g₁ = s * u * ξ ^ (N - a i) := by
      have h1 : (t * g₁ - s * u * ξ ^ (N - a i)) * ξ ^ a i = 0 := by
        have e1 : ξ ^ a i * t * g₁ = s * u * ξ ^ N := by
          calc ξ ^ a i * t * g₁ = (s * Δ) * g₁ := by rw [hst]
            _ = s * u * (g * g₁) := by rw [hΔ]; ring
            _ = s * u * ξ ^ N := by rw [hgg]
        rw [← hsplit] at e1
        linear_combination e1
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow (a i))).mp h1
      exact sub_eq_zero.mp this
    refine ⟨s' * u' * t, ?_, ⟨t' * s * u, ?_⟩⟩
    · simp only [map_mul]
      exact mul_ne_zero (mul_ne_zero hs' (hu' i)) ht
    · calc s' * u' * t * (g' * g₁) = (s' * Δ') * (t * g₁) := by rw [hΔ']; ring
        _ = ξ ^ a i * t' * (s * u * ξ ^ (N - a i)) := by rw [hst', key]
        _ = (ξ ^ a i * ξ ^ (N - a i)) * (t' * s * u) := by ring
        _ = ξ ^ N * (t' * s * u) := by rw [hsplit]
  obtain ⟨b, hb⟩ := GlobalTheory.T.divisibility_of_vanishing_powers R C ι f ξ hξ hf0 hker N (g' * g₁) hloc
  have hg₁ : g₁ ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have : x * ξ ^ N = 0 := by rw [← hgg, ← mul_assoc, mul_comm x g, mul_assoc, hx, mul_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow N)).mp this
  refine ⟨b, ?_⟩
  have h2 : (g' - g * b) * g₁ = 0 := by
    rw [sub_mul, hb, ← hgg]; ring
  exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hg₁).mp h2)

end GlobalTheory.DetInv
